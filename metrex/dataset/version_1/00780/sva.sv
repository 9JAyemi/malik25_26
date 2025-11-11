// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        RST,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        sub,
  input logic        cin,
  input logic        select,
  input logic        cout,
  input logic        overflow,
  input logic [7:0]  q,
  input logic [3:0]  counter,
  input logic [3:0]  adder_out,
  input logic [3:0]  selected_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!RST);

  // Asynchronous reset clears (checked at reset edge)
  property p_async_reset_clears;
    @(negedge RST) 1'b1 |=> (counter==4'b0 && adder_out==4'b0 && selected_out==4'b0 &&
                             cout==1'b0 && overflow==1'b0 && q==8'b0);
  endproperty
  assert property (p_async_reset_clears);

  // No X/Z on key outputs when active
  assert property (RST |-> !$isunknown({cout, overflow, q}));

  // Counter increments modulo-16
  assert property ($past(RST) |-> counter == ($past(counter) + 4'd1));

  // adder_out captures combinational adder_in of previous cycle
  assert property ($past(RST) |->
                   adder_out == $past( sub ? (a - b - cin) : (a + b + cin) ));

  // selected_out muxes previous-cycle sources
  assert property ($past(RST) |->
                   selected_out == ($past(select) ? $past(adder_out) : $past(counter)));

  // {cout,q} is 9-bit zero-extended sum of previous-cycle selected_out + counter
  assert property ($past(RST) |->
                   {cout, q} == ({4'b0, $past(selected_out)} + {4'b0, $past(counter)}));

  // Signed 4-bit overflow of previous-cycle add (intent-level check)
  assert property ($past(RST) |->
                   overflow == ( ($past(selected_out[3]) == $past(counter[3])) &&
                                 ($past(selected_out[3]) != (($past(selected_out)+$past(counter))[3])) ));

  // Optional: structural consequence of above sum (high bits zero)
  assert property ($past(RST) |-> (cout==1'b0 && q[7:5]==3'b000));

  // Key functional coverage
  cover property ($past(RST) && (sub==1'b0) && (cin==1'b0));
  cover property ($past(RST) && (sub==1'b1) && (cin==1'b1));
  cover property ($past(RST) && (select==1'b0));
  cover property ($past(RST) && (select==1'b1));
  cover property ($past(RST) && overflow);
  cover property ($past(RST) && ($past(counter)==4'hF) && (counter==4'h0));

endmodule

// Bind into DUT (accesses internals via port connections)
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .RST(RST),
  .a(a),
  .b(b),
  .sub(sub),
  .cin(cin),
  .select(select),
  .cout(cout),
  .overflow(overflow),
  .q(q),
  .counter(counter),
  .adder_out(adder_out),
  .selected_out(selected_out)
);