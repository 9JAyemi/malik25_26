// SVA for buf_interm_disable
// Bind this file to the DUT. Focused, concise checks + coverage.

module buf_interm_disable_sva #(
  parameter string SIM_DEVICE      = "7SERIES",
  parameter string USE_IBUFDISABLE = "TRUE"
)(
  input  logic I,
  input  logic IBUFDISABLE,
  input  logic INTERMDISABLE,
  output logic O
);

  // Expected constant for out_val per SIM_DEVICE
  localparam logic EXP_OUT_VAL = (SIM_DEVICE == "7SERIES") ? 1'b1 : 1'b0;

  // Parameter sanity (static)
  initial begin
    assert (USE_IBUFDISABLE == "TRUE" || USE_IBUFDISABLE == "FALSE")
      else $error("USE_IBUFDISABLE must be \"TRUE\" or \"FALSE\"");
  end

  // Combinational functional equivalence checks
  always_comb begin
    if (USE_IBUFDISABLE == "TRUE") begin
      if (IBUFDISABLE === 1'b0) begin
        assert (O === I)
          else $error("O must follow I when IBUFDISABLE==0");
      end
      else if (IBUFDISABLE === 1'b1) begin
        assert (O === EXP_OUT_VAL)
          else $error("O must be %0b when IBUFDISABLE==1", EXP_OUT_VAL);
      end
      else begin
        assert (O === 1'bx)
          else $error("O must be X when IBUFDISABLE is X/Z");
      end
    end
    else begin
      assert (O === I)
        else $error("O must equal I when USE_IBUFDISABLE != \"TRUE\"");
    end
  end

  // INTERMDISABLE must have no effect on O
  property intermdisable_no_effect;
    @(posedge INTERMDISABLE or negedge INTERMDISABLE)
      $stable(I) && $stable(IBUFDISABLE) |-> $stable(O);
  endproperty
  assert property (intermdisable_no_effect);

  // Coverage
  if (USE_IBUFDISABLE == "TRUE") begin
    // O follows I when enabled
    cover property (@(posedge I)  IBUFDISABLE===1'b0 && O===I);
    cover property (@(negedge I)  IBUFDISABLE===1'b0 && O===I);
    // O drives constant per SIM_DEVICE when disabled
    cover property (@(posedge IBUFDISABLE) IBUFDISABLE===1'b1 && O===EXP_OUT_VAL);
    // Exercise INTERMDISABLE activity (no functional effect)
    cover property (@(posedge INTERMDISABLE) 1);
    cover property (@(negedge INTERMDISABLE) 1);
    // Invalid IBUFDISABLE produces X on O
    cover property (@(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE)
                    (IBUFDISABLE !== 1'b0 && IBUFDISABLE !== 1'b1) ##0 (O===1'bx));
  end
  else begin
    // O always follows I when IBUFDISABLE is unused
    cover property (@(posedge I)  O===I);
    cover property (@(negedge I)  O===I);
  end

endmodule

// Bind into DUT (parameters propagate from the instance)
bind buf_interm_disable
  buf_interm_disable_sva #(.SIM_DEVICE(SIM_DEVICE), .USE_IBUFDISABLE(USE_IBUFDISABLE))
  buf_interm_disable_sva_i (.*);