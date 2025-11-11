// SVA for core_pc
module core_pc_sva #(parameter logic [31:0] initial_addr = 32'h0004_0000)
(
  input  logic        clk,
  input  logic        rst,
  input  logic        pc_go,
  input  logic        stall,
  input  logic        id_pc_src,
  input  logic        btb_v,
  input  logic [1:0]  btb_type,
  input  logic [31:0] btb_target,
  input  logic [31:0] ras_target,
  input  logic [31:0] good_target,
  input  logic [31:0] pc_out,
  input  logic [31:0] pc_plus4,
  input  logic        v_pc_out
);

  // Reset behavior
  assert property (@(posedge clk) rst |=> pc_out == initial_addr);

  // Hold when not advancing (stall or !pc_go)
  assert property (@(posedge clk) disable iff (rst)
                   !(pc_go && !stall) |=> pc_out == $past(pc_out));

  // Next-PC update and source selection
  assert property (@(posedge clk) disable iff (rst)
    (pc_go && !stall) |=> pc_out ==
      ($past(id_pc_src) ? $past(good_target) :
       ($past(btb_v) && ($past(btb_type) inside {2'b00,2'b01,2'b10})) ? $past(btb_target) :
       ($past(btb_v) && ($past(btb_type) == 2'b11)) ? $past(ras_target) :
       ($past(pc_out) + 32'd4)));

  // v_pc_out is the advance qualifier
  assert property (@(posedge clk) v_pc_out == (pc_go && !stall));

  // pc_plus4 correctness
  assert property (@(posedge clk) pc_plus4 == pc_out + 32'd4);

  // Basic X/Z checks on outputs (after reset)
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown({pc_out, pc_plus4, v_pc_out}));

  // Coverage: exercise each next-PC source on an advance
  cover property (@(posedge clk) disable iff (rst)
                  pc_go && !stall && id_pc_src ##1 pc_out == $past(good_target));

  cover property (@(posedge clk) disable iff (rst)
                  pc_go && !stall && !id_pc_src && btb_v &&
                  (btb_type inside {2'b00,2'b01,2'b10})
                  ##1 pc_out == $past(btb_target));

  cover property (@(posedge clk) disable iff (rst)
                  pc_go && !stall && !id_pc_src && btb_v && (btb_type == 2'b11)
                  ##1 pc_out == $past(ras_target));

  cover property (@(posedge clk) disable iff (rst)
                  pc_go && !stall && !id_pc_src && !btb_v
                  ##1 pc_out == $past(pc_out) + 32'd4);

  // Coverage: hold due to stall and due to !pc_go
  cover property (@(posedge clk) disable iff (rst)
                  stall && pc_go ##1 pc_out == $past(pc_out));

  cover property (@(posedge clk) disable iff (rst)
                  !pc_go ##1 pc_out == $past(pc_out));

  // Coverage: reset then first valid advance
  cover property (@(posedge clk) rst ##1 !rst ##[1:$] (pc_go && !stall));
endmodule

// Bind into the DUT
bind core_pc core_pc_sva #(.initial_addr(initial_addr)) core_pc_sva_b (.*);