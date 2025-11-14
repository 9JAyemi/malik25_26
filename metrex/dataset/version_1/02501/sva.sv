// SVA for memory_to_color
// Bindable, event-clocked (combinational) assertions with concise full coverage.

module memory_to_color_sva (
  input  logic [1:0]  color_depth_i,
  input  logic [31:0] mem_i,
  input  logic [1:0]  mem_lsb_i,
  input  logic [31:0] color_o,
  input  logic [3:0]  sel_o
);
  // Combinational sampling event
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Depth encodings
  localparam logic [1:0] DEPTH8  = 2'b00;
  localparam logic [1:0] DEPTH16 = 2'b01;
  localparam logic [1:0] DEPTH32 = 2'b10;

  // 8-bit selections
  assert property (color_depth_i==DEPTH8 && mem_lsb_i==2'b00 |-> sel_o===4'b0001 && color_o=== {8'h00, mem_i[31:24], 8'h00, 8'h00});
  assert property (color_depth_i==DEPTH8 && mem_lsb_i==2'b01 |-> sel_o===4'b0010 && color_o=== {8'h00, 8'h00, mem_i[23:16], 8'h00});
  assert property (color_depth_i==DEPTH8 && mem_lsb_i==2'b10 |-> sel_o===4'b0100 && color_o=== {8'h00, 8'h00, 8'h00, mem_i[15:8]});
  assert property (color_depth_i==DEPTH8 && mem_lsb_i==2'b11 |-> sel_o===4'b1000 && color_o=== {8'h00, 8'h00, 8'h00, mem_i[7:0]});

  // 16-bit selections (only mem_lsb_i==00 or 01 are legal)
  assert property (color_depth_i==DEPTH16 && mem_lsb_i==2'b00 |-> sel_o===4'b0011 && color_o=== {mem_i[31:16], 16'h0000});
  assert property (color_depth_i==DEPTH16 && mem_lsb_i==2'b01 |-> sel_o===4'b1100 && color_o=== {16'h0000, mem_i[15:0]});
  assert property (color_depth_i==DEPTH16 && (mem_lsb_i inside {2'b10,2'b11}) |-> $isunknown(sel_o) && $isunknown(color_o));

  // 32-bit selection
  assert property (color_depth_i==DEPTH32 |-> sel_o===4'b1111 && color_o===mem_i);

  // Illegal depth -> X on outputs
  assert property ((color_depth_i==2'b11) |-> $isunknown(sel_o) && $isunknown(color_o));

  // Structural sanity on sel patterns for valid modes
  assert property (color_depth_i==DEPTH8  |-> $onehot(sel_o));
  assert property (color_depth_i==DEPTH16 && (mem_lsb_i inside {2'b00,2'b01}) |-> ($countones(sel_o)==2) && (sel_o inside {4'b0011,4'b1100}));
  assert property (color_depth_i==DEPTH32 |-> sel_o===4'b1111);

  // Coverage: hit every branch (valid and illegal)
  cover property (color_depth_i==DEPTH8  && mem_lsb_i==2'b00);
  cover property (color_depth_i==DEPTH8  && mem_lsb_i==2'b01);
  cover property (color_depth_i==DEPTH8  && mem_lsb_i==2'b10);
  cover property (color_depth_i==DEPTH8  && mem_lsb_i==2'b11);
  cover property (color_depth_i==DEPTH16 && mem_lsb_i==2'b00);
  cover property (color_depth_i==DEPTH16 && mem_lsb_i==2'b01);
  cover property (color_depth_i==DEPTH16 && mem_lsb_i==2'b10); // illegal branch
  cover property (color_depth_i==DEPTH16 && mem_lsb_i==2'b11); // illegal branch
  cover property (color_depth_i==DEPTH32);
  cover property (color_depth_i==2'b11); // illegal depth
endmodule

// Bind into DUT
bind memory_to_color memory_to_color_sva sva_i (
  .color_depth_i(color_depth_i),
  .mem_i        (mem_i),
  .mem_lsb_i    (mem_lsb_i),
  .color_o      (color_o),
  .sel_o        (sel_o)
);