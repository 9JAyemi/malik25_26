// SVA checker for multiple_of_3
module multiple_of_3_sva (input logic [2:0] data, input logic q);

  // Sample on every simulation tick; use ##0 to avoid preponed sampling races
  default clocking cb @($global_clock); endclocking

  // Golden model
  function automatic logic exp_mult3(input logic [2:0] d);
    return (d == 3'd0) || (d == 3'd3) || (d == 3'd6);
  endfunction

  // No X/Z on q when input is known
  a_no_x: assert property ( !$isunknown(data) |-> ##0 !$isunknown(q) )
    else $error("q is X/Z when data is known");

  // Functional correctness: q must match multiple-of-3 truth
  a_func: assert property ( !$isunknown(data) |-> ##0 (q == exp_mult3(data)) )
    else $error("q != multiple_of_3(data): data=%0d q=%0b", data, q);

  // Basic activity coverage on q
  c_q0:   cover property (##0 (q == 1'b0));
  c_q1:   cover property (##0 (q == 1'b1));

  // Full input-output mapping coverage for all 3-bit values
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : C
      localparam logic [2:0] VAL = i[2:0];
      localparam bit EXP = ((i % 3) == 0);
      c_val: cover property ( (data == VAL) ##0 (q == EXP) );
    end
  endgenerate

endmodule

// Bind the checker to the DUT
bind multiple_of_3 multiple_of_3_sva u_multiple_of_3_sva (.data(data), .q(q));