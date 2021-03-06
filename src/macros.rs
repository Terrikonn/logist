/// The standard logging macro.
///
/// This macro will generically log with the specified `Level` and `format!`
/// based argument list.
///
/// # Examples
///
/// ```edition2018
/// use logist::{log, Level};
///
/// # fn main() {
/// let data = (42, "Forty-two");
/// let private_data = "private";
///
/// log!(Level::Error, "Received errors: {}, {}", data.0, data.1);
/// log!(target: "app_events", Level::Warn, "App warning: {}, {}, {}",
///     data.0, data.1, private_data);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! log {
    (target: $target:expr, $lvl:expr, $($arg:tt)+) => ({
        let lvl = $lvl;
        if lvl <= $crate::STATIC_MAX_LEVEL && lvl <= $crate::max_level() {
            $crate::__private_api_log(
                __log_format_args!($($arg)+),
                lvl,
                &($target, __log_module_path!(), __log_file!(), __log_line!()),
            );
        }
    });
    ($lvl:expr, $($arg:tt)+) => (log!(target: __log_module_path!(), $lvl, $($arg)+))
}

/// Logs a message at the emergency level.
///
/// # Examples
///
/// ```edition2018
/// use logist::emerg;
///
/// # fn main() {
/// emerg!("System is unusable!");
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! emerg{
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Emerg, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Emerg, $($arg)+)
    )
}

/// Logs a message at the alert level.
///
/// # Examples
///
/// ```edition2018
/// use logist::alert;
///
/// # fn main() {
/// alert!("Action must be taken immediately");
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! alert {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Alert, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Alert, $($arg)+)
    )
}

/// Logs a message at the critical level.
///
/// # Examples
///
/// ```edition2018
/// use logist::crit;
///
/// # fn main() {
/// crit!("Unexpected input");
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! crit {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Crit, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Crit, $($arg)+)
    )
}

/// Logs a message at the error level.
///
/// # Examples
///
/// ```edition2018
/// use logist::error;
///
/// # fn main() {
/// let (err_info, port) = ("No connection", 22);
///
/// error!("Error: {} on port {}", err_info, port);
/// error!(target: "app_events", "App Error: {}, Port: {}", err_info, 22);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! error {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Error, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Error, $($arg)+)
    )
}

/// Logs a message at the warn level.
///
/// # Examples
///
/// ```edition2018
/// use logist::warn;
///
/// # fn main() {
/// let warn_description = "Invalid Input";
///
/// warn!("Warning! {}!", warn_description);
/// warn!(target: "input_events", "App received warning: {}", warn_description);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! warn {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Warn, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Warn, $($arg)+)
    )
}

/// Logs a message at the notice level.
///
/// # Examples
///
/// ```edition2018
/// use logist::notice;
///
/// # fn main() {
/// notice!("An error event which we have reconciled");
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! notice {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Notice, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Notice, $($arg)+)
    )
}

/// Logs a message at the info level.
///
/// # Examples
///
/// ```edition2018
/// use logist::info;
///
/// # fn main() {
/// # struct Connection { port: u32, speed: f32 }
/// let conn_info = Connection { port: 40, speed: 3.20 };
///
/// info!("Connected to port {} at {} Mb/s", conn_info.port, conn_info.speed);
/// info!(target: "connection_events", "Successfull connection, port: {}, speed: {}",
///       conn_info.port, conn_info.speed);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! info {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Info, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Info, $($arg)+)
    )
}

/// Logs a message at the debug level.
///
/// # Examples
///
/// ```edition2018
/// use logist::debug;
///
/// # fn main() {
/// # struct Position { x: f32, y: f32 }
/// let pos = Position { x: 3.234, y: -1.223 };
///
/// debug!("New position: x: {}, y: {}", pos.x, pos.y);
/// debug!(target: "app_events", "New position: x: {}, y: {}", pos.x, pos.y);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! debug {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, $crate::Level::Debug, $($arg)+)
    );
    ($($arg:tt)+) => (
        log!($crate::Level::Debug, $($arg)+)
    )
}

/// Determines if a message logged at the specified level in that module will
/// be logged.
///
/// This can be used to avoid expensive computation of log message arguments if
/// the message would be ignored anyway.
///
/// # Examples
///
/// ```edition2018
/// use logist::Level::Debug;
/// use logist::{debug, log_enabled};
///
/// # fn foo() {
/// if log_enabled!(Debug) {
///     let data = expensive_call();
///     debug!("expensive debug data: {} {}", data.x, data.y);
/// }
/// if log_enabled!(target: "Global", Debug) {
///    let data = expensive_call();
///    debug!(target: "Global", "expensive debug data: {} {}", data.x, data.y);
/// }
/// # }
/// # struct Data { x: u32, y: u32 }
/// # fn expensive_call() -> Data { Data { x: 0, y: 0 } }
/// # fn main() {}
/// ```
#[macro_export(local_inner_macros)]
macro_rules! log_enabled {
    (target: $target:expr, $lvl:expr) => {{
        let lvl = $lvl;
        lvl <= $crate::STATIC_MAX_LEVEL &&
            lvl <= $crate::max_level() &&
            $crate::__private_api_enabled(lvl, $target)
    }};
    ($lvl:expr) => {
        log_enabled!(target: __log_module_path!(), $lvl)
    };
}

// The log macro above cannot invoke format_args directly because it uses
// local_inner_macros. A format_args invocation there would resolve to
// $crate::format_args which does not exist. Instead invoke format_args here
// outside of local_inner_macros so that it resolves (probably) to
// core::format_args or std::format_args. Same for the several macros that
// follow.
//
// This is a workaround until we drop support for pre-1.30 compilers. At that
// point we can remove use of local_inner_macros, use $crate:: when invoking
// local macros, and invoke format_args directly.
#[doc(hidden)]
#[macro_export]
macro_rules! __log_format_args {
    ($($args:tt)*) => {
        format_args!($($args)*)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __log_module_path {
    () => {
        module_path!()
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __log_file {
    () => {
        file!()
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __log_line {
    () => {
        line!()
    };
}
