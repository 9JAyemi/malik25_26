// SVA for sky130_fd_sc_hd__nor4
// Bindable, concise, and checks function, 4-state behavior, and buffer transparency.

module sky130_fd_sc_hd__nor4_sva (
  input logic Y,
  input logic A, B, C, D,
  input logic nor0_out_Y
);

  // Convenience event: trigger on any relevant edge
  // (replicated inline to keep pure SVA event expressions)

  // Functional equivalence after delta cycle on any input edge
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge C or negedge C or
                     posedge D or negedge D)
                   ##0 (Y === ~(A | B | C | D)))
    else $error("NOR4 functional mismatch: Y != ~(A|B|C|D)");

  // Deterministic 4-state behavior: any 1 forces Y=0
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge C or negedge C or
                     posedge D or negedge D)
                   (((A===1) || (B===1) || (C===1) || (D===1)) |-> ##0 (Y===1'b0)))
    else $error("NOR4: Y not 0 when some input is 1");

  // Deterministic 4-state behavior: all 0 forces Y=1
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge C or negedge C or
                     posedge D or negedge D)
                   (((A===0) && (B===0) && (C===0) && (D===0)) |-> ##0 (Y===1'b1)))
    else $error("NOR4: Y not 1 when all inputs are 0");

  // X/Z propagation: if no input is 1 and some is X/Z, Y must be X
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge C or negedge C or
                     posedge D or negedge D)
                   ( !(A===1 || B===1 || C===1 || D===1) &&
                     ( (A===1'bx)||(A===1'bz) ||
                       (B===1'bx)||(B===1'bz) ||
                       (C===1'bx)||(C===1'bz) ||
                       (D===1'bx)||(D===1'bz) )
                     |-> ##0 (Y===1'bx)))
    else $error("NOR4: Y must be X when inputs contain X/Z and none is 1");

  // Output must never be Z
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge C or negedge C or
                     posedge D or negedge D or
                     posedge Y or negedge Y)
                   !(Y===1'bz))
    else $error("NOR4: Y is high-Z");

  // Buffer transparency: Y equals internal nor output after delta
  assert property (@(posedge nor0_out_Y or negedge nor0_out_Y or
                     posedge Y or negedge Y)
                   ##0 (Y === nor0_out_Y))
    else $error("NOR4 buffer mismatch: Y != nor0_out_Y");

  // Coverage
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ((A===0)&&(B===0)&&(C===0)&&(D===0)) ##0 (Y===1));  // all-zeros case

  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ((A===1)&&(B===0)&&(C===0)&&(D===0)) ##0 (Y===0));
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ((A===0)&&(B===1)&&(C===0)&&(D===0)) ##0 (Y===0));
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ((A===0)&&(B===0)&&(C===1)&&(D===0)) ##0 (Y===0));
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ((A===0)&&(B===0)&&(C===0)&&(D===1)) ##0 (Y===0));

  // X/Z propagation coverage
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C or
                    posedge D or negedge D)
                  ( !(A===1 || B===1 || C===1 || D===1) &&
                    ( (A===1'bx)||(A===1'bz) ||
                      (B===1'bx)||(B===1'bz) ||
                      (C===1'bx)||(C===1'bz) ||
                      (D===1'bx)||(D===1'bz) )
                    ##0 (Y===1'bx)));

  // Y toggles both ways
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__nor4 sky130_fd_sc_hd__nor4_sva
  nor4_sva_i (.Y(Y), .A(A), .B(B), .C(C), .D(D), .nor0_out_Y(nor0_out_Y));