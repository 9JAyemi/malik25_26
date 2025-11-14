// SVA for MaquinaDeControl
module MaquinaDeControl_sva (
  input  logic Clock,
  input  logic Reset,        // active-low
  input  logic NewScanCode,
  input  logic NewAscii,
  input  logic LoadDato,
  input  logic LoadChar,
  input  logic ScanCodeType
);

  default clocking cb @(posedge Clock); endclocking

  // Output-derived "state" decodes
  let is_sleep     = ({LoadDato,LoadChar,ScanCodeType} == 3'b000);
  let is_recibido  = ({LoadDato,LoadChar,ScanCodeType} == 3'b100);
  let is_type      = ({LoadDato,LoadChar,ScanCodeType} == 3'b001);
  let is_new       = ({LoadDato,LoadChar,ScanCodeType} == 3'b010);

  // Outputs must be one of the four legal encodings
  assert property (cb.disable iff (!Reset)
    {LoadDato,LoadChar,ScanCodeType} inside {3'b000,3'b100,3'b001,3'b010}
  );

  // No X/Z on outputs in active operation
  assert property (cb.disable iff (!Reset)
    !$isunknown({LoadDato,LoadChar,ScanCodeType})
  );

  // Async reset holds Sleep encoding throughout reset low
  property async_reset_forces_sleep;
    @(negedge Reset) 1 |-> ({LoadDato,LoadChar,ScanCodeType}==3'b000) throughout (!Reset);
  endproperty
  assert property (async_reset_forces_sleep);

  // FSM next-state behavior (via outputs)
  // Sleep: hold without NewScanCode
  assert property (cb.disable iff (!Reset)
    is_sleep && !NewScanCode |=> is_sleep
  );

  // Sleep: NewScanCode advances to Recibido
  assert property (cb.disable iff (!Reset)
    is_sleep && NewScanCode |=> is_recibido
  );

  // Recibido -> Type
  assert property (cb.disable iff (!Reset)
    is_recibido |=> is_type
  );

  // Type -> Sleep (per RTL as written)
  assert property (cb.disable iff (!Reset)
    is_type |=> is_sleep
  );

  // New -> Sleep
  assert property (cb.disable iff (!Reset)
    is_new |=> is_sleep
  );

  // End-to-end scan flow: Sleep + NewScanCode -> Recibido -> Type -> Sleep
  assert property (cb.disable iff (!Reset)
    is_sleep && NewScanCode |=> is_recibido ##1 is_type ##1 is_sleep
  );

  // Coverage
  cover property (cb is_sleep && !NewScanCode |=> is_sleep);
  cover property (cb is_sleep && NewScanCode |=> is_recibido ##1 is_type ##1 is_sleep);
  cover property (cb is_recibido);
  cover property (cb is_type);
  cover property (cb is_new); // may be unreachable with current RTL
  cover property (cb is_type &&  NewAscii |=> is_sleep); // shows NewAscii doesn't change outcome
  cover property (cb is_type && !NewAscii |=> is_sleep);

endmodule

bind MaquinaDeControl MaquinaDeControl_sva sva_i (.*);