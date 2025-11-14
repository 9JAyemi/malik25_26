// SVA for Traductor
module Traductor_sva (input logic clk, rst,
                      input logic [3:0] in,
                      input logic [10:0] out);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [10:0] map(input logic [3:0] v);
    case (v)
      4'h0: map = 11'd1666;
      4'h1: map = 11'd999;
      4'h2: map = 11'd666;
      4'h3: map = 11'd499;
      4'h4: map = 11'd399;
      4'h5: map = 11'd332;
      4'h6: map = 11'd285;
      4'h7: map = 11'd249;
      4'h8: map = 11'd221;
      4'h9: map = 11'd199;
      4'hA: map = 11'd181;
      4'hB: map = 11'd165;
      4'hC: map = 11'd152;
      4'hD: map = 11'd141;
      4'hE: map = 11'd132;
      4'hF: map = 11'd124;
      default: map = 11'd0;
    endcase
  endfunction

  // Asynchronous reset behavior
  assert property (@(posedge rst) out == 11'd0);
  assert property (rst |-> (out == 11'd0) until_with (!rst));

  // Core mapping check (registered, no latency beyond the clock edge)
  assert property (disable iff (rst) out == map(in));

  // Output limited to legal set when not in reset
  assert property (disable iff (rst)
    out inside {11'd1666,11'd999,11'd666,11'd499,11'd399,11'd332,11'd285,11'd249,
                11'd221,11'd199,11'd181,11'd165,11'd152,11'd141,11'd132,11'd124});

  // No X/Z on output when active
  assert property (disable iff (rst) !$isunknown(out));

  // First cycle after reset deassert maps correctly
  assert property ($fell(rst) |-> out == map(in));

  // Functional coverage: exercise all input codes and mapped outputs
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cg
      cover property (disable iff (rst) in == i[3:0] && out == map(i[3:0]));
    end
  endgenerate
  cover property (@(posedge rst) 1'b1);
  cover property ($fell(rst));

endmodule

bind Traductor Traductor_sva sva_i (.*);