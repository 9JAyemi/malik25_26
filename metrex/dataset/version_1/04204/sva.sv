// SVA for the provided DUTs. Bind these into the compiled design.

// ---------------- rotator_module SVA ----------------
module rotator_module_sva (
  input  logic        clk,
  input  logic        load,
  input  logic [1:0]  ena,
  input  logic [99:0] data_in,
  input  logic [99:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Controls known after first cycle
  assert property (past_valid |-> !$isunknown({load, ena}));

  // Load has priority: next state equals sampled data_in
  assert property (disable iff (!past_valid)
                   load |=> data_out == $past(data_in));

  // Rotate left by 1 when ena==01 (no load)
  assert property (disable iff (!past_valid)
                   !load && ena==2'b01 |=> data_out == { $past(data_out)[98:0], $past(data_out)[99] });

  // Rotate right by 1 when ena==10 (no load)
  assert property (disable iff (!past_valid)
                   !load && ena==2'b10 |=> data_out == { $past(data_out)[1:99], $past(data_out)[0] });

  // Hold otherwise (ena==00 or 11) when not loading
  assert property (disable iff (!past_valid)
                   !load && !(ena inside {2'b01,2'b10}) |=> data_out == $past(data_out));

  // Coverage: full 100-step rotations return to start
  property p_full_left;
    logic [99:0] s;
    (!load && ena==2'b01, s = data_out)
      ##1 (!load && ena==2'b01)[*99]
      ##1 data_out == s;
  endproperty
  cover property (p_full_left);

  property p_full_right;
    logic [99:0] s;
    (!load && ena==2'b10, s = data_out)
      ##1 (!load && ena==2'b10)[*99]
      ##1 data_out == s;
  endproperty
  cover property (p_full_right);
endmodule

bind rotator_module rotator_module_sva
  (.clk(clk), .load(load), .ena(ena), .data_in(data_in), .data_out(data_out));


// ---------------- top_module SVA (covers mux + OR functionality) ----------------
module top_module_sva (
  input  logic        clk,
  input  logic [99:0] data0,
  input  logic [99:0] data1,
  input  logic [99:0] data2,
  input  logic [99:0] data3,
  input  logic [99:0] data4,
  input  logic [99:0] data5,
  input  logic [2:0]  sel,
  input  logic [99:0] mux_out,
  input  logic [99:0] rotator_out,
  input  logic [99:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Functional OR correctness
  assert property (q == (rotator_out | mux_out));

  // Mux correctness for valid selects
  assert property (sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101}
                   |-> mux_out == (sel==3'b000 ? data0 :
                                   sel==3'b001 ? data1 :
                                   sel==3'b010 ? data2 :
                                   sel==3'b011 ? data3 :
                                   sel==3'b100 ? data4 : data5));

  // Default behavior for invalid/other selects
  assert property (!(sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101})
                   |-> mux_out == data0);

  // Coverage: hit each select, including default
  cover property (sel==3'b000);
  cover property (sel==3'b001);
  cover property (sel==3'b010);
  cover property (sel==3'b011);
  cover property (sel==3'b100);
  cover property (sel==3'b101);
  cover property (!(sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101}));
endmodule

bind top_module top_module_sva
  (.clk(clk),
   .data0(data0), .data1(data1), .data2(data2), .data3(data3), .data4(data4), .data5(data5),
   .sel(sel),
   .mux_out(mux_out),
   .rotator_out(rotator_out),
   .q(q));