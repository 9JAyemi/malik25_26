// SVA checker for ff_inv
// Bind with:  bind ff_inv ff_inv_sva ff_inv_sva_i(.*);

module ff_inv_sva (
  input  logic               clk,
  input  logic               reset,
  input  logic [255:0]       rx_a,
  input  logic [255:0]       rx_p,
  input  logic               tx_done,
  input  logic [255:0]       tx_a,

  // Internals
  input  logic [255:0]       u, v, x, y,
  input  logic               x_carry, y_carry,
  input  logic               u_even, v_even,
  input  logic [256:0]       u_minus_v, v_minus_u,
  input  logic [256:0]       x_adder, y_adder
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic combinational correctness
  assert property ( (u_even === (u[0] == 1'b0)) && (v_even === (v[0] == 1'b0)) );
  assert property ( (x_carry || y_carry || u_even || v_even)
                    |-> (x_adder == ({1'b0,x} + {1'b0,rx_p}) &&
                         y_adder == ({1'b0,y} + {1'b0,rx_p})) );
  assert property ( !(x_carry || y_carry) && !(u_even || v_even)
                    |-> (x_adder == ({1'b0,x} - {1'b0,y}) &&
                         y_adder == ({1'b0,y} - {1'b0,x})) );

  // Synchronous reset effect (one cycle later)
  assert property (disable iff (1'b0)
                   @(posedge clk) reset |=> (u==rx_a && v==rx_p &&
                                              x==256'd1 && y==256'd0 &&
                                              !x_carry && !y_carry && !tx_done));

  // tx_done behavior
  assert property (tx_done |=> tx_done);                     // sticky until reset
  assert property ($rose(tx_done) |-> ($past(u)==256'd1 || $past(v)==256'd1));
  assert property ($rose(tx_done) && $past(u)==256'd1 |-> tx_a == $past(x));
  assert property ($rose(tx_done) && $past(u)!=256'd1 && $past(v)==256'd1 |-> tx_a == $past(y));
  assert property (tx_done |=> $stable(tx_a));               // tx_a stable while done

  // Carry-fix path has highest priority and only updates selected regs
  assert property ($past(x_carry || y_carry) |-> u==$past(u) && v==$past(v));
  assert property ($past(x_carry || y_carry) |-> !x_carry && !y_carry);

  assert property ($past(x_carry) |-> x == $past(x_adder[255:0]));
  assert property (!$past(x_carry) && $past(y_carry) |-> x == $past(x));

  assert property ($past(y_carry) |-> y == $past(y_adder[255:0]));
  assert property (!$past(y_carry) && $past(x_carry) |-> y == $past(y));

  // Even path updates (no carry pending)
  // u even branch
  assert property (!$past(x_carry || y_carry) && $past(u_even) |-> u == ($past(u) >> 1));
  assert property (!$past(x_carry || y_carry) && $past(u_even) && $past(x[0]==1'b0)
                   |-> x == ($past(x) >> 1));
  assert property (!$past(x_carry || y_carry) && $past(u_even) && $past(x[0]==1'b1)
                   |-> x == $past(x_adder[256:1]));

  // v even branch
  assert property (!$past(x_carry || y_carry) && $past(v_even) |-> v == ($past(v) >> 1));
  assert property (!$past(x_carry || y_carry) && $past(v_even) && $past(y[0]==1'b0)
                   |-> y == ($past(y) >> 1));
  assert property (!$past(x_carry || y_carry) && $past(v_even) && $past(y[0]==1'b1)
                   |-> y == $past(y_adder[256:1]));

  // Even path does not (re)introduce carry flags
  assert property (!$past(x_carry || y_carry) && ($past(u_even) || $past(v_even))
                   |-> !x_carry && !y_carry);

  // Subtract path (both odd, no carry pending)
  // Case u >= v
  assert property (!$past(x_carry || y_carry) && !$past(u_even || v_even) &&
                   $past(u_minus_v[256]==1'b0)
                   |-> u == $past(u_minus_v[255:0]) &&
                       v == $past(v) &&
                       x == $past(x_adder[255:0]) &&
                       y == $past(y) &&
                       x_carry == $past(x_adder[256]) &&
                       !y_carry);

  // Case v > u
  assert property (!$past(x_carry || y_carry) && !$past(u_even || v_even) &&
                   $past(u_minus_v[256]==1'b1)
                   |-> v == $past(v_minus_u[255:0]) &&
                       u == $past(u) &&
                       y == $past(y_adder[255:0]) &&
                       x == $past(x) &&
                       y_carry == $past(y_adder[256]) &&
                       !x_carry);

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property ($rose(tx_done) && $past(u)==256'd1);
  cover property ($rose(tx_done) && $past(v)==256'd1 && $past(u)!=256'd1);
  cover property ($past(!(x_carry||y_carry)) && $past(u_even) && $past(v_even));
  cover property ($past(!(x_carry||y_carry)) && !$past(u_even||v_even) && $past(u_minus_v[256]==1'b0));
  cover property ($past(!(x_carry||y_carry)) && !$past(u_even||v_even) && $past(u_minus_v[256]==1'b1));
  cover property ($past(x_carry));
  cover property ($past(y_carry));

endmodule

// Bind into DUT scope to access internals by name
bind ff_inv ff_inv_sva ff_inv_sva_i(.*);