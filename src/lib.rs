//! A logging facade combining log lightweightness and tracing structure logging
//! with more log levels from linux syslog
#![warn(missing_docs)]
#![deny(missing_debug_implementations)]
#![cfg_attr(any(not(feature = "std"), not(test)), no_std)]

extern crate no_std_compat as std;
#[macro_use]
extern crate cfg_if;

#[cfg(has_atomics)]
use std::sync::atomic::AtomicUsize;
use std::{
    cmp,
    fmt,
    mem,
    prelude::v1::*,
    str::FromStr,
    sync::atomic::Ordering,
    usize,
};

#[cfg(feature = "std")]
use ::std::error;

#[macro_use]
mod macros;

cfg_if! { if #[cfg(not(has_atomics))] {
use std::cell::Cell;

struct AtomicUsize {
    value: Cell<usize>,
}

impl AtomicUsize {
    const fn new(value: usize) -> Self {
        Self { value: Cell::new(v) }
    }

    fn load(&self, _order: Ordering) -> usize {
        self.value.get()
    }

    fn store(&self, value: usize, _order: Ordering) {
        setl.value.set(value);
    }

    #[cfg(atomic_cas)]
    fn compare_exchange(
        &self,
        current: usize,
        new: usize,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<usize, usize>
    {
        let previous = self.value.get();

        if current == previous {
            self.value.set(new);
        }

        Ok(previous)
    }
}

// Any platform withotu atomics is unlikely to have multiple cores, so
// writing via Cell will not be a race condition.
unsafe impl Sync for AtomicUsize {}
}}

// The LOGGER static holds a pointer to the global logger. It is protected by
// the STATE static which determines whether LOGGER has been initialized yet.
static mut LOGGER: &dyn Log = &NopLogger;

static STATE: AtomicUsize = AtomicUsize::new(0);

// There are three different states that we care about: the logger's
// uninitialized, the logger's initializing(set_logger's been called but
// LOGGER hasn't actually been set yet), or the logger's active.
const UNINITIALIZED: usize = 0;
const INITIALIZING: usize = 1;
const INITIALIZED: usize = 2;

static MAX_LOG_LEVEL_FILTER: AtomicUsize = AtomicUsize::new(0);

static LOG_LEVEL_NAMES: [&str; 9] = [
    "OFF",
    "EMERGENCY",
    "ALERT",
    "CRIT",
    "ERROR",
    "WARN",
    "NOTICE",
    "INFO",
    "DEBUG",
];

static SET_LOGGER_ERROR: &str =
    "attempted to set a logger after the logging system was already initialized";
static LEVEL_PARSE_ERROR: &str =
    "attempted to convert a string that doesn't match an existing log level";
/// An enum representing the available verbosity levels of the logger.
///
/// Typical usage includes: checking if a certain `Level` is enabled with
/// [`log_enabled!`](macro.log_enabled.html), specifying the `Level` of
/// [`log!`](macro.log.html), and comparing a `Level` directly to a
/// [`LevelFilter`](enum.LevelFilter.html).
#[repr(usize)]
#[derive(Copy, Eq, Debug, Hash)]
pub enum Level {
    /// System is unusable
    Emergency = 1,
    /// Action must be taken immediately
    Alert = 2,
    /// Critical conditions
    Crit = 3,
    /// Error conditions
    Error = 4,
    /// Warning conditions
    Warn = 5,
    /// Normal but significant condition
    Notice = 6,
    /// Informational messages
    Info = 7,
    /// Debug-level messages
    Debug = 8,
}

impl Clone for Level {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        *self as usize == *other as usize
    }
}

impl PartialEq<LevelFilter> for Level {
    fn eq(&self, other: &LevelFilter) -> bool {
        *self as usize == *other as usize
    }
}

impl PartialOrd for Level {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }

    fn lt(&self, other: &Self) -> bool {
        (*self as usize) < (*other as usize)
    }

    fn le(&self, other: &Self) -> bool {
        (*self as usize) <= (*other as usize)
    }

    fn gt(&self, other: &Self) -> bool {
        (*self as usize) > (*other as usize)
    }

    fn ge(&self, other: &Self) -> bool {
        (*self as usize) >= (*other as usize)
    }
}

impl PartialOrd<LevelFilter> for Level {
    fn partial_cmp(&self, other: &LevelFilter) -> Option<cmp::Ordering> {
        Some((*self as usize).cmp(&(*other as usize)))
    }

    fn lt(&self, other: &LevelFilter) -> bool {
        (*self as usize) < (*other as usize)
    }

    fn le(&self, other: &LevelFilter) -> bool {
        (*self as usize) <= (*other as usize)
    }

    fn gt(&self, other: &LevelFilter) -> bool {
        (*self as usize) > (*other as usize)
    }

    fn ge(&self, other: &LevelFilter) -> bool {
        (*self as usize) >= (*other as usize)
    }
}

impl Ord for Level {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (*self as usize).cmp(&(*other as usize))
    }
}

impl FromStr for Level {
    type Err = ParseLevelError;

    fn from_str(level: &str) -> Result<Self, Self::Err> {
        LOG_LEVEL_NAMES
            .iter()
            .position(|&name| name.eq_ignore_ascii_case(level))
            .into_iter()
            .filter(|&idx| idx != 0)
            .map(|idx| Self::from_usize(idx).unwrap())
            .next()
            .ok_or(ParseLevelError)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.pad(self.as_str())
    }
}

impl Level {
    fn from_usize(u: usize) -> Option<Self> {
        match u {
            1 => Some(Self::Emergency),
            2 => Some(Self::Alert),
            3 => Some(Self::Crit),
            4 => Some(Self::Error),
            5 => Some(Self::Warn),
            6 => Some(Self::Notice),
            7 => Some(Self::Info),
            8 => Some(Self::Debug),
            _ => None,
        }
    }

    /// Returns the most verbose logging level.
    pub fn max() -> Self {
        Self::Debug
    }

    /// Converts the `Level` to the equivalent `LevelFilter`.
    pub fn to_level_filter(&self) -> LevelFilter {
        LevelFilter::from_usize(*self as usize).unwrap()
    }

    /// Returns the string representation of the `Level`.
    ///
    /// This returns the same string as the `fmt::Display` implementation.
    pub fn as_str(&self) -> &'static str {
        LOG_LEVEL_NAMES[*self as usize]
    }
}

/// An enum representing the available verbosity level filters of the logger.
///
/// A `LevelFilter` may be compared directly to a [`Level`]. Use this type to
/// get and set the maximum log level with [`max_level()`] and
/// [`set_max_level`].
///
/// [`Level`]: enum.Level.html
/// [`max_level()`]: fn.max_level.html
/// [`set_max_level`]: fn.set_max_level.html
#[repr(usize)]
#[derive(Copy, Eq, Debug, Hash)]
pub enum LevelFilter {
    /// A level lower than all log levels.
    Off = 0,
    /// Corresponds to the `Emergency` log level.
    Emergency = 1,
    /// Corresponds to the `Alert` log level.
    Alert = 2,
    /// Corresponds to the `Crit` log level.
    Crit = 3,
    /// Corresponds to the `Error` log level.
    Error = 4,
    /// Corresponds to the `Warn` log level.
    Warn = 5,
    /// Corresponds to the `Notice` log level.
    Notice = 6,
    /// Corresponds to the `Info` log level.
    Info = 7,
    /// Corresponds to the `Debug` log level.
    Debug = 8,
}

impl Clone for LevelFilter {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for LevelFilter {
    fn eq(&self, other: &Self) -> bool {
        *self as usize == *other as usize
    }
}

impl PartialEq<Level> for LevelFilter {
    fn eq(&self, other: &Level) -> bool {
        *self as usize == *other as usize
    }
}

impl PartialOrd for LevelFilter {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }

    fn lt(&self, other: &Self) -> bool {
        (*self as usize) < (*other as usize)
    }

    fn le(&self, other: &Self) -> bool {
        (*self as usize) <= (*other as usize)
    }

    fn gt(&self, other: &Self) -> bool {
        (*self as usize) > (*other as usize)
    }

    fn ge(&self, other: &Self) -> bool {
        (*self as usize) >= (*other as usize)
    }
}

impl PartialOrd<Level> for LevelFilter {
    fn partial_cmp(&self, other: &Level) -> Option<cmp::Ordering> {
        Some((*self as usize).cmp(&(*other as usize)))
    }

    fn lt(&self, other: &Level) -> bool {
        (*self as usize) < (*other as usize)
    }

    fn le(&self, other: &Level) -> bool {
        (*self as usize) <= (*other as usize)
    }

    fn gt(&self, other: &Level) -> bool {
        (*self as usize) > (*other as usize)
    }

    fn ge(&self, other: &Level) -> bool {
        (*self as usize) >= (*other as usize)
    }
}

impl Ord for LevelFilter {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (*self as usize).cmp(&(*other as usize))
    }
}

impl FromStr for LevelFilter {
    type Err = ParseLevelError;

    fn from_str(level: &str) -> Result<LevelFilter, Self::Err> {
        LOG_LEVEL_NAMES
            .iter()
            .position(|&name| name.eq_ignore_ascii_case(level))
            .map(|p| Self::from_usize(p).unwrap())
            .ok_or(ParseLevelError)
    }
}

impl fmt::Display for LevelFilter {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.pad(self.as_str())
    }
}

impl LevelFilter {
    fn from_usize(u: usize) -> Option<Self> {
        match u {
            0 => Some(Self::Off),
            1 => Some(Self::Emergency),
            2 => Some(Self::Alert),
            3 => Some(Self::Crit),
            4 => Some(Self::Error),
            5 => Some(Self::Warn),
            6 => Some(Self::Notice),
            7 => Some(Self::Info),
            8 => Some(Self::Debug),
            _ => None,
        }
    }

    /// Returns the most verbose logging level.
    pub fn max() -> Self {
        Self::Debug
    }

    /// Converts the `LevelFilter` to the equivalent `Level`.
    ///
    /// Returns `None` if `self` is `LevelFilter::Off`,
    pub fn to_level(&self) -> Option<Level> {
        Level::from_usize(*self as usize)
    }

    /// Returns the string representation of the `LevelFilter`.
    ///
    /// This returns the same string as the `fmt::Display` implementation.
    pub fn as_str(&self) -> &'static str {
        LOG_LEVEL_NAMES[*self as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum MaybeStaticStr<'a> {
    Static(&'static str),
    Borrowed(&'a str),
}

impl<'a> MaybeStaticStr<'a> {
    fn get(&self) -> &'a str {
        match *self {
            MaybeStaticStr::Static(s) => s,
            MaybeStaticStr::Borrowed(s) => s,
        }
    }
}

/// The "payload" of a log message.
///
/// # Use
///
/// `Record` structures are passed as parameters to the [`log`][method.log]
/// method of the [`Log`] trait. Logger implementors manipulate these
/// structures in order to display log messages. `Record`s are automatically
/// created by the [`log!`] macro and so are not seen by log users.
///
/// Note that the [`level()`] and [`target()`] accessors are equivalent to
/// `self.metadata().level()` and `self.metadata().target()` respectively.
/// These methods are provided as a convenience for users of this structure.
///
/// # Example
///
/// The following example shows a simple logger that displays the level,
/// module path, and message of any `Record` that is passed to it.
///
/// ```edition2018
/// struct SimpleLogger;
///
/// impl logist::Log for SimpleLogger {
///    fn enabled(&self, metadata: &logist::Metadata) -> bool {
///        true
///    }
///
///    fn log(&self, record: &logist::Record) {
///        if !self.enabled(record.metadata()) {
///            return;
///        }
///
///        println!("{}:{} -- {}",
///                 record.level(),
///                 record.target(),
///                 record.args());
///    }
///    fn flush(&self) {}
/// }
/// ```
///
/// [method.log]: trait.Log.html#tymethod.log
/// [`Log`]: trait.Log.html
/// [`log!`]: macro.log.html
/// [`level()`]: struct.Record.html#method.level
/// [`target()`]: struct.Record.html#method.target
#[derive(Clone, Debug)]
pub struct Record<'a> {
    metadata: Metadata<'a>,
    args: fmt::Arguments<'a>,
    module_path: Option<MaybeStaticStr<'a>>,
    file: Option<MaybeStaticStr<'a>>,
    line: Option<u32>,
}

impl<'a> Record<'a> {
    /// Returns a new builder.
    pub fn builder() -> RecordBuilder<'a> {
        RecordBuilder::new()
    }

    /// The message body.
    pub fn args(&self) -> &fmt::Arguments<'a> {
        &self.args
    }

    /// Metadata about the log directive.
    pub fn metadata(&self) -> &Metadata<'a> {
        &self.metadata
    }

    /// The verbosity level of the message.
    pub fn level(&self) -> Level {
        self.metadata.level()
    }

    /// The name of the target of the directive.
    pub fn target(&self) -> &'a str {
        self.metadata.target()
    }

    /// The module path of the message.
    pub fn module_path(&self) -> Option<&'a str> {
        self.module_path.map(|s| s.get())
    }

    /// The module path of the message, if it is a `'static` string.
    pub fn module_path_static(&self) -> Option<&'static str> {
        match self.module_path {
            Some(MaybeStaticStr::Static(s)) => Some(s),
            _ => None,
        }
    }

    /// The source file containing the message.
    pub fn file(&self) -> Option<&'a str> {
        self.file.map(|s| s.get())
    }

    /// The module path of the message, if it is a `'static` string.
    pub fn file_static(&self) -> Option<&'static str> {
        match self.file {
            Some(MaybeStaticStr::Static(s)) => Some(s),
            _ => None,
        }
    }

    /// The line containing the message.
    pub fn line(&self) -> Option<u32> {
        self.line
    }
}

/// Builder for [`Record`](struct.Record.html).
///
/// Typically should only be used by log library creators or for testing and
/// "shim loggers". The `RecordBuilder` can set the different parameters of
/// `Record` object, and returns the created object when `build` is called.
///
/// # Examples
///
///
/// ```edition2018
/// use logist::{Level, Record};
///
/// let record = Record::builder()
///                 .args(format_args!("Error!"))
///                 .level(Level::Error)
///                 .target("myApp")
///                 .file(Some("server.rs"))
///                 .line(Some(144))
///                 .module_path(Some("server"))
///                 .build();
/// ```
///
/// Alternatively, use [`MetadataBuilder`](struct.MetadataBuilder.html):
///
/// ```edition2018
/// use logist::{Record, Level, MetadataBuilder};
///
/// let error_metadata = MetadataBuilder::new()
///                         .target("myApp")
///                         .level(Level::Error)
///                         .build();
///
/// let record = Record::builder()
///                 .metadata(error_metadata)
///                 .args(format_args!("Error!"))
///                 .line(Some(433))
///                 .file(Some("app.rs"))
///                 .module_path(Some("server"))
///                 .build();
/// ```
#[derive(Debug)]
pub struct RecordBuilder<'a> {
    record: Record<'a>,
}

impl<'a> RecordBuilder<'a> {
    /// Construct new `RecordBuilder`.
    ///
    /// The default options are:
    ///
    /// - `args`: [`format_args!("")`]
    /// - `metadata`: [`Metadata::builder().build()`]
    /// - `module_path`: `None`
    /// - `file`: `None`
    /// - `line`: `None`
    ///
    /// [`format_args!("")`]: https://doc.rust-lang.org/std/macro.format_args.html
    /// [`Metadata::builder().build()`]:
    /// struct.MetadataBuilder.html#method.build
    pub fn new() -> RecordBuilder<'a> {
        RecordBuilder {
            record: Record {
                args: format_args!(""),
                metadata: Metadata::builder().build(),
                module_path: None,
                file: None,
                line: None,
            },
        }
    }

    /// Set [`args`](struct.Record.html#method.args).
    pub fn args(&mut self, args: fmt::Arguments<'a>) -> &mut RecordBuilder<'a> {
        self.record.args = args;
        self
    }

    /// Set [`metadata`](struct.Record.html#method.metadata). Construct a
    /// `Metadata` object with [`MetadataBuilder`](struct.MetadataBuilder.html).
    pub fn metadata(&mut self, metadata: Metadata<'a>) -> &mut RecordBuilder<'a> {
        self.record.metadata = metadata;
        self
    }

    /// Set [`Metadata::level`](struct.Metadata.html#method.level).
    pub fn level(&mut self, level: Level) -> &mut RecordBuilder<'a> {
        self.record.metadata.level = level;
        self
    }

    /// Set [`Metadata::target`](struct.Metadata.html#method.target)
    pub fn target(&mut self, target: &'a str) -> &mut RecordBuilder<'a> {
        self.record.metadata.target = target;
        self
    }

    /// Set [`module_path`](struct.Record.html#method.module_path)
    pub fn module_path(&mut self, path: Option<&'a str>) -> &mut RecordBuilder<'a> {
        self.record.module_path = path.map(MaybeStaticStr::Borrowed);
        self
    }

    /// Set [`module_path`](struct.Record.html#method.module_path) to a
    /// `'static` string
    pub fn module_path_static(&mut self, path: Option<&'static str>) -> &mut RecordBuilder<'a> {
        self.record.module_path = path.map(MaybeStaticStr::Static);
        self
    }

    /// Set [`file`](struct.Record.html#method.file)
    pub fn file(&mut self, file: Option<&'a str>) -> &mut RecordBuilder<'a> {
        self.record.file = file.map(MaybeStaticStr::Borrowed);
        self
    }

    /// Set [`file`](struct.Record.html#method.file) to a `'static` string.
    pub fn file_static(&mut self, file: Option<&'static str>) -> &mut RecordBuilder<'a> {
        self.record.file = file.map(MaybeStaticStr::Static);
        self
    }

    /// Set [`line`](struct.Record.html#method.line)
    pub fn line(&mut self, line: Option<u32>) -> &mut RecordBuilder<'a> {
        self.record.line = line;
        self
    }

    /// Invoke the builder and return a `Record`
    pub fn build(&self) -> Record<'a> {
        self.record.clone()
    }
}

/// Metadata about a log message.
///
/// # Use
///
/// `Metadata` structs are created when users of the library use
/// logging macros.
///
/// They are consumed by implementations of the `Log` trait in the
/// `enabled` method.
///
/// `Record`s use `Metadata` to determine the log message's severity
/// and target.
///
/// Users should use the `log_enabled!` macro in their code to avoid
/// constructing expensive log messages.
///
/// # Examples
///
/// ```edition2018
/// use logist::{Record, Level, Metadata};
///
/// struct MyLogger;
///
/// impl logist::Log for MyLogger {
///     fn enabled(&self, metadata: &Metadata) -> bool {
///         metadata.level() <= Level::Info
///     }
///
///     fn log(&self, record: &Record) {
///         if self.enabled(record.metadata()) {
///             println!("{} - {}", record.level(), record.args());
///         }
///     }
///     fn flush(&self) {}
/// }
///
/// # fn main(){}
/// ```
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Metadata<'a> {
    level: Level,
    target: &'a str,
}

impl<'a> Metadata<'a> {
    /// Returns a new builder.
    pub fn builder() -> MetadataBuilder<'a> {
        MetadataBuilder::new()
    }

    /// The verbosity level of the message.
    pub fn level(&self) -> Level {
        self.level
    }

    /// The name of the target of the directive.
    pub fn target(&self) -> &'a str {
        self.target
    }
}

/// Builder for [`Metadata`](struct.Metadata.html).
///
/// Typically should only be used by log library creators or for testing and
/// "shim loggers". The `MetadataBuilder` can set the different parameters of a
/// `Metadata` object, and returns the created object when `build` is called.
///
/// # Example
///
/// ```edition2018
/// let target = "myApp";
/// use logist::{Level, MetadataBuilder};
/// let metadata = MetadataBuilder::new()
///                     .level(Level::Debug)
///                     .target(target)
///                     .build();
/// ```
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct MetadataBuilder<'a> {
    metadata: Metadata<'a>,
}

impl<'a> MetadataBuilder<'a> {
    /// Construct a new `MetadataBuilder`.
    ///
    /// The default options are:
    ///
    /// - `level`: `Level::Informational`
    /// - `target`: `""`
    pub fn new() -> MetadataBuilder<'a> {
        MetadataBuilder {
            metadata: Metadata {
                level: Level::Info,
                target: "",
            },
        }
    }

    /// Setter for [`level`](struct.Metadata.html#method.level).
    pub fn level(&mut self, arg: Level) -> &mut MetadataBuilder<'a> {
        self.metadata.level = arg;
        self
    }

    /// Setter for [`target`](struct.Metadata.html#method.target).
    pub fn target(&mut self, target: &'a str) -> &mut MetadataBuilder<'a> {
        self.metadata.target = target;
        self
    }

    /// Returns a `Metadata` object.
    pub fn build(&self) -> Metadata<'a> {
        self.metadata.clone()
    }
}

/// A trait encapsulating the operations required of a logger.
pub trait Log: Send + Sync {
    /// Determines if a log message with the specified metadata would be
    /// logged.
    ///
    /// This is used by the `log_enabled!` macro to allow callers to avoid
    /// expensive computation of log message arguments if the message would be
    /// discarded anyway.
    fn enabled(&self, metadata: &Metadata) -> bool;

    /// Log the `Record`.
    ///
    /// Note that `enabled` is *not* necessarily called before this method.
    /// Implementations of `log` shoudl perform all necessary filtering
    /// internally.
    fn log(&self, record: &Record);

    /// Flushes any buffered records.
    fn flush(&self);
}

// Just used as a dummy initial value for LOGGER
struct NopLogger;

impl Log for NopLogger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        false
    }

    fn log(&self, _record: &Record) {}

    fn flush(&self) {}
}

#[cfg(feature = "std")]
impl<T> Log for std::boxed::Box<T>
where
    T: ?Sized + Log,
{
    fn enabled(&self, metadata: &Metadata) -> bool {
        self.as_ref().enabled(metadata)
    }

    fn log(&self, record: &Record) {
        self.as_ref().log(record);
    }

    fn flush(&self) {
        self.as_ref().flush();
    }
}

/// Sets the global maximum log level.
///
/// Generally, this should only be called by the active logging implementation.
pub fn set_max_level(level: LevelFilter) {
    MAX_LOG_LEVEL_FILTER.store(level as usize, Ordering::SeqCst);
}

/// Returns the current maximum log level.
///
/// The [`log!`], [`emergency!`], [`alert!`], [`cirtical!`], [`error!`],
/// [`warning!`], [`notice!`], [`informational!`] and [`debug!`] macros check
/// this value and discard any message logged at a higher level. The maximum
/// log level is set by the [`set_max_level`] function.
///
/// [`log!`]: macro.log.html
/// [`emergency!`]: macro.emergency.html
/// [`alert!`]: macro.alert.html
/// [`critical!`]: macro.critical.html
/// [`error!`]: macro.error.html
/// [`warning!`]: macro.warning.html
/// [`notice!`]: macro.notice.html
/// [`informational!`]: macro.informational.html
/// [`debug!`]: macro.debug.html
/// [`set_max_level`]: fn.set_max_level.html
#[inline(always)]
pub fn max_level() -> LevelFilter {
    // Since `LevelFilter` is `repr(usize)`,
    // this transmute is sound if and only if `MAX_LOG_LEVEL_FILTER`
    // is set to a usize that is a valid discriminant for `LevelFilter`.
    // Since `MAX_LOG_LEVEL_FILTER` is private, the only time it's set
    // is by `set_max_level` above, i.e. by casting a `LevelFilter` to `usize`.
    // So any usize stored in `MAX_LOG_LEVEL_FILTER` is a valid discriminant.
    unsafe { mem::transmute(MAX_LOG_LEVEL_FILTER.load(Ordering::Relaxed)) }
}

/// Sets the global logger to a `Box<Log>`.
///
/// This is a simple convenience wrapper over `set_logger`, which takes a
/// `Box<Log>` rather than a `&'static Log`. See the documentation for
/// [`set_logger`] for more details.
///
/// Requires the `std` feature.
///
/// # Errors
///
/// An error is returned if a logger has already been set.
///
/// [`set_logger`]: fn.set_logger.html
#[cfg(all(feature = "std", atomic_cas))]
pub fn set_boxed_logger(logger: Box<dyn Log>) -> Result<(), SetLoggerError> {
    set_logger_inner(|| Box::leak(logger))
}

/// Sets the global logger to a `&'static Log`.
///
/// This function may only be called once in the lifetime of a program. Any log
/// events that occur before the call to `set_logger` completes will be ignored.
///
/// This function does not typically need to be called manually. Logger
/// implementations should provide an initialization method that installs the
/// logger internally.
///
/// # Availability
///
/// This method is available even when the `std` feature is disabled. However,
/// it is currently unavailable on `thumbv6` targets, which lack support for
/// some atomic operations which are used by this function. Even on those
/// targets, [`set_logger_racy`] will be available.
///
/// # Errors
///
/// An error is returned if a logger has already been set.
///
/// # Examples
///
/// ```edition2018
/// use logist::{error, info, warn, Record, Level, Metadata, LevelFilter};
///
/// static MY_LOGGER: MyLogger = MyLogger;
///
/// struct MyLogger;
///
/// impl logist::Log for MyLogger {
///     fn enabled(&self, metadata: &Metadata) -> bool {
///         metadata.level() <= Level::Info
///     }
///
///     fn log(&self, record: &Record) {
///         if self.enabled(record.metadata()) {
///             println!("{} - {}", record.level(), record.args());
///         }
///     }
///     fn flush(&self) {}
/// }
///
/// # fn main(){
/// logist::set_logger(&MY_LOGGER).unwrap();
/// logist::set_max_level(LevelFilter::Info);
///
/// info!("hello log");
/// warn!("warning");
/// error!("oops");
/// # }
/// ```
///
/// [`set_logger_racy`]: fn.set_logger_racy.html
#[cfg(atomic_cas)]
pub fn set_logger(logger: &'static dyn Log) -> Result<(), SetLoggerError> {
    set_logger_inner(|| logger)
}

#[cfg(atomic_cas)]
fn set_logger_inner<F>(make_logger: F) -> Result<(), SetLoggerError>
where
    F: FnOnce() -> &'static dyn Log,
{
    let old_state = match STATE.compare_exchange(
        UNINITIALIZED,
        INITIALIZING,
        Ordering::SeqCst,
        Ordering::SeqCst,
    ) {
        Ok(s) | Err(s) => s,
    };
    match old_state {
        UNINITIALIZED => {
            unsafe {
                LOGGER = make_logger();
            }
            STATE.store(INITIALIZED, Ordering::SeqCst);
            Ok(())
        },
        INITIALIZING => {
            while STATE.load(Ordering::SeqCst) == INITIALIZING {
                std::hint::spin_loop();
            }
            Err(SetLoggerError)
        },
        _ => Err(SetLoggerError),
    }
}

/// A thread-unsafe version of [`set_logger`].
///
/// This function is available on all platforms, even those that do not have
/// support for atomics that is needed by [`set_logger`].
///
/// In almost all cases, [`set_logger`] should be preferred.
///
/// # Safety
///
/// This function is only safe to call when no other logger initialization
/// function is called while this function still executes.
///
/// This can be upheld by (for example) making sure that **there are no other
/// threads**, and (on embedded) that **interrupts are disabled**.
///
/// It is safe to use other logging functions while this function runs
/// (including all logging macros).
///
/// [`set_logger`]: fn.set_logger.html
pub unsafe fn set_logger_racy(logger: &'static dyn Log) -> Result<(), SetLoggerError> {
    match STATE.load(Ordering::SeqCst) {
        UNINITIALIZED => {
            LOGGER = logger;
            STATE.store(INITIALIZED, Ordering::SeqCst);
            Ok(())
        },
        INITIALIZING => {
            // This is just plain UB, since we were racing another initialization function
            unreachable!("set_logger_racy must not be used with other initialization functions")
        },
        _ => Err(SetLoggerError),
    }
}

/// The type returned by [`set_logger`] if [`set_logger`] has already been
/// called.
///
/// [`set_logger`]: fn.set_logger.html
#[allow(missing_copy_implementations)]
#[derive(Debug)]
pub struct SetLoggerError;

impl fmt::Display for SetLoggerError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(SET_LOGGER_ERROR)
    }
}

// The Error trait is not available in libcore
#[cfg(feature = "std")]
impl error::Error for SetLoggerError {}

/// The type returned by [`from_str`] when the string doesn't match any of the
/// log levels.
///
/// [`from_str`]: https://doc.rust-lang.org/std/str/trait.FromStr.html#tymethod.from_str
#[allow(missing_copy_implementations)]
#[derive(Debug, PartialEq)]
pub struct ParseLevelError;

impl fmt::Display for ParseLevelError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(LEVEL_PARSE_ERROR)
    }
}

// The Error trait is not available in libcore
#[cfg(feature = "std")]
impl error::Error for ParseLevelError {}

/// Returns a reference to the logger
///
/// If a logger has not been set, a no-op implementation is retunred.
pub fn logger() -> &'static dyn Log {
    if STATE.load(Ordering::SeqCst) != INITIALIZED {
        static NOP: NopLogger = NopLogger;
        &NOP
    } else {
        unsafe { LOGGER }
    }
}

// WARNING: this is not part of the crate's public API and is subject to change
// at any time
#[doc(hidden)]
pub fn __private_api_log(
    args: fmt::Arguments,
    level: Level,
    &(target, module_path, file, line): &(&str, &'static str, &'static str, u32),
) {
    logger().log(
        &Record::builder()
            .args(args)
            .level(level)
            .target(target)
            .module_path_static(Some(module_path))
            .file_static(Some(file))
            .line(Some(line))
            .build(),
    );
}

// WARNING: this is not part of the crate's public API and is subject to change
// at any time
#[doc(hidden)]
pub fn __private_api_enabled(level: Level, target: &str) -> bool {
    logger().enabled(&Metadata::builder().level(level).target(target).build())
}

/// The statically resolved maximum log level.
///
/// See the crate level documentation for information on how to configure this.
///
/// This value is checked by the log macros, but not by the `Log`ger returned by
/// the [`logger`] function. Code that manually calls functions on that value
/// should compare the level against this value.
///
/// [`logger`]: fn.logger.html
pub const STATIC_MAX_LEVEL: LevelFilter = MAX_LEVEL_INNER;

cfg_if! {
    if #[cfg(all(not(debug_assertions), feature = "release_max_level_off"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Off;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_emergency"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Emergency;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_alert"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Alert;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_ciritcal"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Crit;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_error"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Error;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_warning"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Warn;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_notice"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Notice;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_informational"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Info;
    } else if #[cfg(all(not(debug_assertions), feature = "release_max_level_debug"))] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Debug;
    } else if #[cfg(feature = "max_level_off")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Off;
    } else if #[cfg(feature = "max_level_emergency")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Emergency;
    } else if #[cfg(feature = "max_level_alert")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Alert;
    } else if #[cfg(feature = "max_level_critical")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Crit;
    } else if #[cfg(feature = "max_level_error")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Error;
    } else if #[cfg(feature = "max_level_warning")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Warn;
    } else if #[cfg(feature = "max_level_notice")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Notice;
    } else if #[cfg(feature = "max_level_informational")] {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Info;
    } else {
        const MAX_LEVEL_INNER: LevelFilter = LevelFilter::Debug;
    }
}

#[cfg(test)]
mod tests {
    use std::string::ToString;

    use super::{
        Level,
        LevelFilter,
        ParseLevelError,
    };

    #[test]
    fn test_levelfilter_from_str() {
        let tests = [
            ("off", Ok(LevelFilter::Off)),
            ("emergency", Ok(LevelFilter::Emergency)),
            ("alert", Ok(LevelFilter::Alert)),
            ("crit", Ok(LevelFilter::Crit)),
            ("error", Ok(LevelFilter::Error)),
            ("warn", Ok(LevelFilter::Warn)),
            ("notice", Ok(LevelFilter::Notice)),
            ("info", Ok(LevelFilter::Info)),
            ("debug", Ok(LevelFilter::Debug)),
            ("OFF", Ok(LevelFilter::Off)),
            ("EMERGENCY", Ok(LevelFilter::Emergency)),
            ("ALERT", Ok(LevelFilter::Alert)),
            ("CRIT", Ok(LevelFilter::Crit)),
            ("ERROR", Ok(LevelFilter::Error)),
            ("WARN", Ok(LevelFilter::Warn)),
            ("NOTICE", Ok(LevelFilter::Notice)),
            ("INFO", Ok(LevelFilter::Info)),
            ("DEBUG", Ok(LevelFilter::Debug)),
            ("asdf", Err(ParseLevelError)),
        ];
        for &(s, ref expected) in &tests {
            assert_eq!(expected, &s.parse());
        }
    }

    #[test]
    fn test_level_from_str() {
        let tests = [
            ("off", Err(ParseLevelError)),
            ("emergency", Ok(Level::Emergency)),
            ("alert", Ok(Level::Alert)),
            ("crit", Ok(Level::Crit)),
            ("error", Ok(Level::Error)),
            ("warn", Ok(Level::Warn)),
            ("notice", Ok(Level::Notice)),
            ("info", Ok(Level::Info)),
            ("debug", Ok(Level::Debug)),
            ("OFF", Err(ParseLevelError)),
            ("EMERGENCY", Ok(Level::Emergency)),
            ("ALERT", Ok(Level::Alert)),
            ("CRIT", Ok(Level::Crit)),
            ("ERROR", Ok(Level::Error)),
            ("WARN", Ok(Level::Warn)),
            ("NOTICE", Ok(Level::Notice)),
            ("INFO", Ok(Level::Info)),
            ("DEBUG", Ok(Level::Debug)),
            ("asdf", Err(ParseLevelError)),
        ];
        for &(s, ref expected) in &tests {
            assert_eq!(expected, &s.parse());
        }
    }

    #[test]
    fn test_level_as_str() {
        let tests = &[
            (Level::Emergency, "EMERGENCY"),
            (Level::Alert, "ALERT"),
            (Level::Crit, "CRIT"),
            (Level::Error, "ERROR"),
            (Level::Warn, "WARN"),
            (Level::Notice, "NOTICE"),
            (Level::Info, "INFO"),
            (Level::Debug, "DEBUG"),
        ];
        for (input, expected) in tests {
            assert_eq!(*expected, input.as_str());
        }
    }

    #[test]
    fn test_level_show() {
        assert_eq!("INFO", Level::Info.to_string());
        assert_eq!("ERROR", Level::Error.to_string());
    }

    #[test]
    fn test_levelfilter_show() {
        assert_eq!("OFF", LevelFilter::Off.to_string());
        assert_eq!("ERROR", LevelFilter::Error.to_string());
    }

    #[test]
    fn test_cross_cmp() {
        assert!(Level::Debug > LevelFilter::Error);
        assert!(LevelFilter::Warn < Level::Debug);
        assert!(LevelFilter::Off < Level::Error);
    }

    #[test]
    fn test_cross_eq() {
        assert!(Level::Error == LevelFilter::Error);
        assert!(LevelFilter::Off != Level::Error);
        assert!(Level::Debug == LevelFilter::Debug);
    }

    #[test]
    fn test_to_level() {
        assert_eq!(Some(Level::Error), LevelFilter::Error.to_level());
        assert_eq!(None, LevelFilter::Off.to_level());
        assert_eq!(Some(Level::Debug), LevelFilter::Debug.to_level());
    }

    #[test]
    fn test_to_level_filter() {
        assert_eq!(LevelFilter::Error, Level::Error.to_level_filter());
        assert_eq!(LevelFilter::Debug, Level::Debug.to_level_filter());
    }

    #[test]
    fn test_level_filter_as_str() {
        let tests = &[
            (LevelFilter::Off, "OFF"),
            (LevelFilter::Emergency, "EMERGENCY"),
            (LevelFilter::Alert, "ALERT"),
            (LevelFilter::Crit, "CRIT"),
            (LevelFilter::Error, "ERROR"),
            (LevelFilter::Warn, "WARN"),
            (LevelFilter::Notice, "NOTICE"),
            (LevelFilter::Info, "INFO"),
            (LevelFilter::Debug, "DEBUG"),
        ];
        for (input, expected) in tests {
            assert_eq!(*expected, input.as_str());
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_error_trait() {
        use super::SetLoggerError;
        let e = SetLoggerError;
        assert_eq!(
            &e.to_string(),
            "attempted to set a logger after the logging system was already initialized"
        );
    }

    #[test]
    fn test_metadata_builder() {
        use super::MetadataBuilder;
        let target = "myApp";
        let metadata_test = MetadataBuilder::new()
            .level(Level::Debug)
            .target(target)
            .build();
        assert_eq!(metadata_test.level(), Level::Debug);
        assert_eq!(metadata_test.target(), "myApp");
    }

    #[test]
    fn test_metadata_convenience_builder() {
        use super::Metadata;
        let target = "myApp";
        let metadata_test = Metadata::builder()
            .level(Level::Debug)
            .target(target)
            .build();
        assert_eq!(metadata_test.level(), Level::Debug);
        assert_eq!(metadata_test.target(), "myApp");
    }

    #[test]
    fn test_record_builder() {
        use super::{
            MetadataBuilder,
            RecordBuilder,
        };
        let target = "myApp";
        let metadata = MetadataBuilder::new().target(target).build();
        let fmt_args = format_args!("hello");
        let record_test = RecordBuilder::new()
            .args(fmt_args)
            .metadata(metadata)
            .module_path(Some("foo"))
            .file(Some("bar"))
            .line(Some(30))
            .build();
        assert_eq!(record_test.metadata().target(), "myApp");
        assert_eq!(record_test.module_path(), Some("foo"));
        assert_eq!(record_test.file(), Some("bar"));
        assert_eq!(record_test.line(), Some(30));
    }

    #[test]
    fn test_record_convenience_builder() {
        use super::{
            Metadata,
            Record,
        };
        let target = "myApp";
        let metadata = Metadata::builder().target(target).build();
        let fmt_args = format_args!("hello");
        let record_test = Record::builder()
            .args(fmt_args)
            .metadata(metadata)
            .module_path(Some("foo"))
            .file(Some("bar"))
            .line(Some(30))
            .build();
        assert_eq!(record_test.target(), "myApp");
        assert_eq!(record_test.module_path(), Some("foo"));
        assert_eq!(record_test.file(), Some("bar"));
        assert_eq!(record_test.line(), Some(30));
    }

    #[test]
    fn test_record_complete_builder() {
        use super::{
            Level,
            Record,
        };
        let target = "myApp";
        let record_test = Record::builder()
            .module_path(Some("foo"))
            .file(Some("bar"))
            .line(Some(30))
            .target(target)
            .level(Level::Error)
            .build();
        assert_eq!(record_test.target(), "myApp");
        assert_eq!(record_test.level(), Level::Error);
        assert_eq!(record_test.module_path(), Some("foo"));
        assert_eq!(record_test.file(), Some("bar"));
        assert_eq!(record_test.line(), Some(30));
    }
}
