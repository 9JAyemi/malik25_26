// SVA checkers for top_module and carry_select_adder

// Checker bound into top_module
module top_module_sva #(
) (
  input  logic        clk,
  input  logic        areset,
  input  logic        load,
  input  logic        ena,
  input  logic        select,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [3:0]  data,
  input  logic [31:0] q,

  // internal signals
  input  logic [31:0] adder_out,
  input  logic [3:0]  shifter_out,
  input  logic [3:0]  buffer [3:0],
  input  logic [1:0]  buffer_ptr,
  input  logic        adder_cin
);

  // Basic sanity
  assert property (@(posedge clk) !$isunknown(areset));
  assert property (@(posedge clk) adder_cin == 1'b0);

  // Reset effects
  assert property (@(posedge clk) areset |-> (q == 32'b0));
  assert property (@(posedge clk) areset |-> (buffer_ptr == 2'b00));

  // Pointer increments every cycle (mod-4), excluding reset cycles
  assert property (@(posedge clk) disable iff (areset)
                   buffer_ptr == $past(buffer_ptr) + 2'b01);

  // Buffer write/hold semantics (use previous index)
  // load has priority over ena
  assert property (@(posedge clk) disable iff (areset)
                   load |=> buffer[$past(buffer_ptr)] == $past(data));

  assert property (@(posedge clk) disable iff (areset)
                   (!load && ena) |=> buffer[$past(buffer_ptr)]
                                      == {1'b0, $past(buffer[$past(buffer_ptr)])[3:1]});

  assert property (@(posedge clk) disable iff (areset)
                   (!load && !ena) |=> buffer[$past(buffer_ptr)]
                                      == $past(buffer[$past(buffer_ptr)]));

  // shifter_out reflects current selected buffer entry
  assert property (@(posedge clk) disable iff (areset)
                   ##1 shifter_out == buffer[buffer_ptr]);

  // Adder correctness at top level (cin is tied 0)
  assert property (@(posedge clk)
                   adder_out == (a + b));

  // q muxing behavior (registered one cycle later)
  assert property (@(posedge clk) disable iff (areset)
                   1'b1 |=> q == ($past(select)
                                  ? $past(adder_out)
                                  : {28'b0, $past(shifter_out)}));

  // When selecting shifter, upper bits must be zero
  assert property (@(posedge clk) disable iff (areset)
                   !$past(select) |-> ##1 q[31:4] == 28'b0);

  // Coverage
  cover property (@(posedge clk) disable iff (areset) $past(buffer_ptr)==2'b11 && buffer_ptr==2'b00); // wrap
  cover property (@(posedge clk) disable iff (areset) load && !ena);
  cover property (@(posedge clk) disable iff (areset) ena && !load);
  cover property (@(posedge clk) disable iff (areset) load && ena);
  cover property (@(posedge clk) disable iff (areset) $past(select)==0 && select==1);
  cover property (@(posedge clk) disable iff (areset) $past(select)==1 && select==0);
  cover property (@(posedge clk) disable iff (areset) !$past(select) ##1 (q != 32'b0)); // shifter path non-zero

endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk        (clk),
  .areset     (areset),
  .load       (load),
  .ena        (ena),
  .select     (select),
  .a          (a),
  .b          (b),
  .data       (data),
  .q          (q),
  .adder_out  (adder_out),
  .shifter_out(shifter_out),
  .buffer     (buffer),
  .buffer_ptr (buffer_ptr),
  .adder_cin  (adder_inst.cin)
);


// Checker bound into carry_select_adder (combinational correctness)
module carry_select_adder_sva (
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        cin,
  input logic [31:0] s,
  input logic        cout
);
  // Sum/carry must match true 33-bit addition at any input change
  assert property (@(a or b or cin or s or cout)
                   {cout, s} == ({1'b0, a} + {1'b0, b} + cin));

  // Coverage: overflow and zero-sum cases
  cover property (@(a or b or cin) ({1'b0, a} + {1'b0, b} + cin)[32] == 1'b1);
  cover property (@(a or b or cin) s == 32'h0000_0000);

endmodule

bind carry_select_adder carry_select_adder_sva u_csa_sva (
  .a   (a),
  .b   (b),
  .cin (cin),
  .s   (s),
  .cout(cout)
);