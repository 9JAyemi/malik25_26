// SVA for AddReg: concise, high-quality checks and coverage
module AddReg_sva (
  input logic clk, rst, load,
  input logic [0:0] D,
  input logic [0:0] Q
);
  default clocking @(posedge clk); endclocking

  // Guard $past on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // X/Z checks
  a_inputs_known: assert property (!$isunknown({rst,load,D}))
    else $error("AddReg: X/Z on inputs");
  a_Q_known: assert property (!$isunknown(Q))
    else $error("AddReg: X/Z on Q");

  // Functional correctness
  a_reset_next_zero: assert property (rst |=> Q == 1'b0)
    else $error("AddReg: Q not 0 after reset");
  a_load_captures_D: assert property (!rst && load |=> Q == $past(D))
    else $error("AddReg: Q not equal to D after load");
  a_normal_update_xor: assert property (!rst && !load |=> Q == $past(Q ^ D))
    else $error("AddReg: Q not updating as Q^D");

  // Coverage
  c_reset:            cover property (rst |=> Q == 1'b0);
  c_load:             cover property (!rst && load |=> Q == $past(D));
  c_hold_when_D0:     cover property (!rst && !load && (D==1'b0) |=> Q == $past(Q));
  c_toggle_when_D1:   cover property (!rst && !load && (D==1'b1) |=> Q == ~$past(Q));
  c_rst_over_load:    cover property (rst && load |=> Q == 1'b0);
endmodule

bind AddReg AddReg_sva sva (.clk(clk), .rst(rst), .load(load), .D(D), .Q(Q));