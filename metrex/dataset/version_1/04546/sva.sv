// Assertions and coverage for fsm_module
// Bind example:
// bind fsm_module fsm_module_sva #( .TIDLE(3'b000), .TCN1(3'b001), .TCN2(3'b010), .TCN3(3'b011), .TCN4(3'b100), .TCN5(3'b101), .IOCLR(3'b110), .TUNU1(3'b111) )
//   fsm_module_sva_i (.*);

module fsm_module_sva
(
  input  [2:0] tstate,
  input        foocr_we,
  input        ioclrinst,
  input        fooc2_qual,
  input  [2:0] ntstate,
  input        ioclrtmout
);
  // Mirror DUT encodings (default match)
  parameter TIDLE = 3'b000;
  parameter TCN1  = 3'b001;
  parameter TCN2  = 3'b010;
  parameter TCN3  = 3'b011;
  parameter TCN4  = 3'b100;
  parameter TCN5  = 3'b101;
  parameter IOCLR = 3'b110;
  parameter TUNU1 = 3'b111;

  // Use any change on inputs/outputs as assertion sampling event
  default clocking cb @(tstate or foocr_we or ioclrinst or fooc2_qual or ntstate or ioclrtmout); endclocking

  // Functional combinational checks (concise, exact spec)
  always_comb begin
    unique case (tstate)
      TIDLE: begin
        assert (ntstate == (foocr_we ? TCN1 : TIDLE) && ioclrtmout == 1'b0)
          else $error("TIDLE next or ioclrtmout mismatch");
      end
      TCN1, TCN2, TCN3, TCN4, TCN5: begin
        assert (ioclrtmout == 1'b0) else $error("ioclrtmout must be 0 in TCN*");
        assert ( (ioclrinst || fooc2_qual) ? (ntstate == TIDLE) :
                 (tstate == TCN5) ? (ntstate == IOCLR) :
                                    (ntstate == tstate + 3'd1) )
          else $error("TCN* next-state mismatch");
      end
      IOCLR: begin
        assert (ntstate == TIDLE && ioclrtmout == 1'b1)
          else $error("IOCLR next/ioclrtmout mismatch");
      end
      TUNU1: begin
        assert (ntstate == TIDLE && ioclrtmout == 1'b0)
          else $error("TUNU1 next/ioclrtmout mismatch");
      end
      default: begin
        assert ($isunknown(ntstate) && $isunknown(ioclrtmout))
          else $error("Invalid tstate must drive X outputs");
      end
    endcase

    // No X on outputs for valid states
    if (tstate inside {TIDLE, TCN1, TCN2, TCN3, TCN4, TCN5, IOCLR, TUNU1})
      assert (!$isunknown({ntstate, ioclrtmout})) else $error("Outputs unknown on valid state");
  end

  // Cross-checks
  assert property ((tstate == IOCLR) |-> (ioclrtmout && ntstate == TIDLE));
  assert property ( ioclrtmout |-> (tstate == IOCLR));

  // Coverage: states and all decision arcs
  cover property (tstate == TIDLE);
  cover property (tstate == TCN1);
  cover property (tstate == TCN2);
  cover property (tstate == TCN3);
  cover property (tstate == TCN4);
  cover property (tstate == TCN5);
  cover property (tstate == IOCLR);
  cover property (tstate == TUNU1);

  // TIDLE arcs
  cover property ((tstate == TIDLE &&  foocr_we) ##0 (ntstate == TCN1 && ioclrtmout == 0));
  cover property ((tstate == TIDLE && !foocr_we) ##0 (ntstate == TIDLE && ioclrtmout == 0));

  // TCN* early return arcs
  cover property (((tstate inside {TCN1,TCN2,TCN3,TCN4,TCN5}) && (ioclrinst || fooc2_qual))
                  ##0 (ntstate == TIDLE && ioclrtmout == 0));

  // Sequential advance arcs
  cover property ((tstate == TCN1 && !(ioclrinst || fooc2_qual)) ##0 (ntstate == TCN2 && ioclrtmout == 0));
  cover property ((tstate == TCN2 && !(ioclrinst || fooc2_qual)) ##0 (ntstate == TCN3 && ioclrtmout == 0));
  cover property ((tstate == TCN3 && !(ioclrinst || fooc2_qual)) ##0 (ntstate == TCN4 && ioclrtmout == 0));
  cover property ((tstate == TCN4 && !(ioclrinst || fooc2_qual)) ##0 (ntstate == TCN5 && ioclrtmout == 0));
  cover property ((tstate == TCN5 && !(ioclrinst || fooc2_qual)) ##0 (ntstate == IOCLR && ioclrtmout == 0));

  // IOCLR and TUNU1 arcs
  cover property ((tstate == IOCLR) ##0 (ntstate == TIDLE && ioclrtmout == 1));
  cover property ((tstate == TUNU1) ##0 (ntstate == TIDLE && ioclrtmout == 0));

  // Coverage: timeout pulse occurrence
  cover property (ioclrtmout && tstate == IOCLR && ntstate == TIDLE);

endmodule