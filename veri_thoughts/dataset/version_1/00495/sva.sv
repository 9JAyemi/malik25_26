// SVA checker for comparator_8bit
module comparator_8bit_sva (
  input  logic        clk,
  input  logic        rst_n,          // active-high enable for checks (disable iff !rst_n)
  input  logic [7:0]  A,
  input  logic [7:0]  B,
  input  logic        equal,
  input  logic        greater_than,
  input  logic        less_than
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on inputs/outputs
  assert property (disable iff (!rst_n) !$isunknown({A,B}));
  assert property (disable iff (!rst_n) !$isunknown({equal,greater_than,less_than}));

  // Exactly one output must be 1 at all times
  assert property (disable iff (!rst_n) $onehot({equal,greater_than,less_than}));

  // Forward correctness (spec -> outputs)
  assert property (disable iff (!rst_n) (A==B) |-> ( equal && !greater_than && !less_than ));
  assert property (disable iff (!rst_n) (A>B)  |-> (!equal &&  greater_than && !less_than));
  assert property (disable iff (!rst_n) (A<B)  |-> (!equal && !greater_than &&  less_than));

  // Backward correctness (outputs -> spec)
  assert property (disable iff (!rst_n) equal        |-> (A==B));
  assert property (disable iff (!rst_n) greater_than |-> (A>B));
  assert property (disable iff (!rst_n) less_than    |-> (A<B));

  // Combinational stability: if inputs hold, outputs hold
  assert property (disable iff (!rst_n) $stable({A,B}) |-> $stable({equal,greater_than,less_than}));

  // Functional coverage: hit all three relations
  cover property (disable iff (!rst_n) (A==B) && equal);
  cover property (disable iff (!rst_n) (A>B)  && greater_than);
  cover property (disable iff (!rst_n) (A<B)  && less_than);

  // Corner coverage
  cover property (disable iff (!rst_n) (A==8'h00 && B==8'h00) && equal);
  cover property (disable iff (!rst_n) (A==8'hFF && B==8'hFF) && equal);
  cover property (disable iff (!rst_n) (A==8'hFF && B==8'h00) && greater_than);
  cover property (disable iff (!rst_n) (A==8'h00 && B==8'hFF) && less_than);

  // Off-by-one edges
  cover property (disable iff (!rst_n) (A == (B + 8'd1)) && greater_than);
  cover property (disable iff (!rst_n) (B == (A + 8'd1)) && less_than);

  // Ordered transition coverage (less -> equal -> greater)
  cover property (disable iff (!rst_n)
                  (A<B && less_than) ##1 (A==B && equal) ##1 (A>B && greater_than));
endmodule

// Example bind (connect clk/rst_n from your environment):
// bind comparator_8bit comparator_8bit_sva u_cmp_sva (.*,.clk(tb_clk),.rst_n(tb_rst_n));