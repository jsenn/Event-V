use vstd::prelude::*;

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus_machine! {

deadlock_free machine Abs {
    ctx {
        max_cars: nat,
    }

    valid(ctx) {
        ctx.max_cars > 0
    }

    state {
        cars: nat,
    }

    init(ctx) {
        cars: 0
    }

    invariant(ctx, state) {
        state.cars <= ctx.max_cars
    }

    event MainlandIn {
        guard(ctx, state) {
            state.cars > 0
        }

        action(ctx, state) {
            Abs {
                cars: (state.cars - 1) as nat,
                ..state
            }
        }
    }

    event MainlandOut {
        guard(ctx, state) {
            state.cars < ctx.max_cars
        }

        action(ctx, state) {
            Abs {
                cars: state.cars + 1,
                ..state
            }
        }
    }
}

}

// ---------------------------------------------------------------------------
// Exec mirror
// ---------------------------------------------------------------------------

verus! {

pub struct AbsExec {
    pub cars: u32,
}

pub struct AbsExecCtx {
    pub max_cars: u32,
}

impl Lift<AbsExec, Abs> for AbsExec {
    open spec fn lift(state: AbsExec) -> Abs {
        Abs { cars: state.cars as nat }
    }
}

impl Lift<AbsExecCtx, Ctx> for AbsExec {
    open spec fn lift(ctx: AbsExecCtx) -> Ctx {
        Ctx { max_cars: ctx.max_cars as nat }
    }
}

impl MirrorContext<AbsExec, Ctx> for AbsExecCtx {
    fn valid(&self) -> (b: bool) {
        self.max_cars > 0
    }
}

impl Mirror<Abs> for AbsExec {
    type ExecCtx = AbsExecCtx;
}

pub struct AbsInit;

impl MirrorInit<AbsExec, Abs, Initialize> for AbsInit {
    type Input = ();

    open spec fn lift_in(_input: &()) -> () { () }

    fn init(_ctx: &AbsExecCtx, _input: &()) -> (state: AbsExec) {
        AbsExec { cars: 0 }
    }
}

pub struct MainlandInMirror;

impl MirrorEvent<AbsExec, Abs, MainlandIn> for MainlandInMirror {
    type Input = ();
    type Output = ();

    open spec fn lift_in(_input: &()) -> () { () }
    open spec fn lift_out(_output: &()) -> () { () }

    fn guard(state: &AbsExec, _ctx: &AbsExecCtx, _input: &()) -> (b: bool) {
        state.cars > 0
    }

    fn action(state: &AbsExec, _ctx: &AbsExecCtx, _input: &()) -> (out: (AbsExec, ())) {
        (AbsExec { cars: state.cars - 1 }, ())
    }
}

pub struct MainlandOutMirror;

impl MirrorEvent<AbsExec, Abs, MainlandOut> for MainlandOutMirror {
    type Input = ();
    type Output = ();

    open spec fn lift_in(_input: &()) -> () { () }
    open spec fn lift_out(_output: &()) -> () { () }

    fn guard(state: &AbsExec, ctx: &AbsExecCtx, _input: &()) -> (b: bool) {
        state.cars < ctx.max_cars
    }

    fn action(state: &AbsExec, _ctx: &AbsExecCtx, _input: &()) -> (out: (AbsExec, ())) {
        (AbsExec { cars: state.cars + 1 }, ())
    }
}

}

// ---------------------------------------------------------------------------
// Runtime adapter
// ---------------------------------------------------------------------------

use verus_machine::animate::{Animate, ContextAdaptor, EventAdaptor, EventSpec, FieldSpec};

impl ContextAdaptor for AbsExecCtx {
    fn fields() -> Vec<FieldSpec> {
        vec![FieldSpec { name: "max_cars", kind: "nat" }]
    }

    fn build(inputs: &[String]) -> Result<Self, String> {
        if inputs.len() != 1 {
            return Err(format!("expected 1 input, got {}", inputs.len()));
        }
        let max_cars: u32 = inputs[0]
            .parse()
            .map_err(|e: std::num::ParseIntError| e.to_string())?;
        Ok(AbsExecCtx { max_cars })
    }
}

#[derive(Debug, Clone)]
pub enum AbsEvent {
    MainlandIn,
    MainlandOut,
}

impl EventAdaptor for AbsEvent {
    fn variants() -> Vec<EventSpec> {
        vec![
            EventSpec { name: "MainlandIn", inputs: vec![] },
            EventSpec { name: "MainlandOut", inputs: vec![] },
        ]
    }

    fn build(name: &str, inputs: &[String]) -> Result<Self, String> {
        if !inputs.is_empty() {
            return Err(format!("{} expects no inputs", name));
        }
        match name {
            "MainlandIn" => Ok(AbsEvent::MainlandIn),
            "MainlandOut" => Ok(AbsEvent::MainlandOut),
            other => Err(format!("unknown event: {}", other)),
        }
    }
}

impl Animate for AbsExec {
    type Ctx = AbsExecCtx;
    type Event = AbsEvent;

    fn init(ctx: &AbsExecCtx) -> Self {
        AbsInit::init(ctx, &())
    }

    fn guard(ctx: &AbsExecCtx, state: &Self, event: &AbsEvent) -> bool {
        match event {
            AbsEvent::MainlandIn => MainlandInMirror::guard(state, ctx, &()),
            AbsEvent::MainlandOut => MainlandOutMirror::guard(state, ctx, &()),
        }
    }

    fn action(ctx: &AbsExecCtx, state: &Self, event: &AbsEvent) -> (Self, Option<String>) {
        match event {
            AbsEvent::MainlandIn => (MainlandInMirror::action(state, ctx, &()).0, None),
            AbsEvent::MainlandOut => (MainlandOutMirror::action(state, ctx, &()).0, None),
        }
    }
}
