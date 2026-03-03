// SVA for RegisterAdd_1
module RegisterAdd_1_sva (
  input logic        clk,
  input logic        rst,
  input logic        load,
  input logic [0:0]  D,
  input logic [0:0]  Q,
  input logic [0:0]  Q_reg,
  input logic [0:0]  Q_next,
  input logic [0:0]  D_reg
);
  // scalar aliases
  wire d   = D[0];
  wire q   = Q[0];
  wire qrg = Q_reg[0];
  wire qn  = Q_next[0];
  wire dr  = D_reg[0];

  default clocking cb @(posedge clk); endclocking

  // Async reset forces Q=0 (checked on clk and rst edges)
  assert property (@(posedge clk or posedge rst) rst |-> (q == 1'b0));

  // Output equals the internal register (continuous assign)
  assert property (q == qrg);

  // 1-cycle functional update: load has priority; else add (XOR) with wrap
  assert property (disable iff (rst)
    1'b1 |=> q == ($past(load) ? $past(d) : ($past(q) ^ $past(d)))
  );

  // Combinational block invariants (when drivers are known)
  assert property ((!$isunknown({load,d,qrg})) |-> (dr == d));
  assert property ((!$isunknown({load,d,qrg})) |-> (qn == (load ? d : (qrg ^ d))));

  // No X on key pins when not in reset
  assert property (disable iff (rst) !$isunknown({load,d,q}));

  // Q only changes on clk rise or rst rise (no glitches)
  assert property (@(posedge q or negedge q) ($rose(clk) || $rose(rst)));

  // Coverage
  cover property (@(posedge rst) 1'b1);
  cover property (@(negedge rst) 1'b1);
  cover property (disable iff (rst) (load && (d==1'b0)) |=> (q == $past(d)));
  cover property (disable iff (rst) (load && (d==1'b1)) |=> (q == $past(d)));
  cover property (disable iff (rst) (!load && d) ##1 (q != $past(q)));     // toggle via add
  cover property (disable iff (rst) (!load && !d) ##1 (q == $past(q)));    // hold via add
  cover property (disable iff (rst) ( q && !load && d) ##1 (q == 1'b0));   // 1+1 -> 0 wrap
  cover property (disable iff (rst) (!q && !load && d) ##1 (q == 1'b1));   // 0+1 -> 1
endmodule

bind RegisterAdd_1 RegisterAdd_1_sva sva (.*);