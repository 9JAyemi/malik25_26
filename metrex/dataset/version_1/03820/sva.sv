// SVA for synchronizer_ff
module synchronizer_ff_sva #(parameter WIDTH=4) (
  input logic              CLK,
  input logic              AR,
  input logic [WIDTH-1:0]  D,
  input logic [WIDTH-1:0]  Q
);

  default clocking cb @(posedge CLK); endclocking

  // Golden next-state relation: Q_next == (AR ? 0 : D)
  property p_next_state;
    logic [WIDTH-1:0] d_s; bit ar_s;
    (d_s = D, ar_s = AR) |=> (Q == (ar_s ? '0 : d_s));
  endproperty
  assert property (p_next_state);

  // Reset dominates: if AR is 1, next Q is 0
  assert property (AR |=> (Q == '0));

  // Coverage
  cover property (AR ##1 (Q == '0)); // observe reset action
  property c_load;
    logic [WIDTH-1:0] d_s;
    (!AR, d_s = D) |=> (Q == d_s);
  endproperty
  cover property (c_load);

  property c_two_loads;
    logic [WIDTH-1:0] d1, d2;
    (!AR, d1=D) ##1 (!AR, d2=D, d2!=d1) |=> (Q == d2);
  endproperty
  cover property (c_two_loads);

  property c_reset_then_load;
    logic [WIDTH-1:0] d;
    AR ##1 (!AR, d = D) ##1 (Q == d);
  endproperty
  cover property (c_reset_then_load);

endmodule

bind synchronizer_ff synchronizer_ff_sva #(.WIDTH(4)) u_synchronizer_ff_sva (.*);