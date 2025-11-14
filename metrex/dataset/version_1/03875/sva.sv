// SVA for stage4_memory. Bind this checker to the DUT.
// Focus: reset behavior, pipeline register capture, combinational WB mux semantics,
// x-propagation, and basic functional coverage.

module stage4_memory_sva (
  input logic        clk_i,
  input logic        rst_i,

  // DUT ports
  input logic [31:0] alu_i,
  input logic        control_load_i,
  input logic        control_store_i,
  input logic        control_take_branch_i,
  input logic        do_wb_i,
  input logic [4:0]  wb_reg_i,
  input logic        stall_o,

  input logic        do_wb_o,
  input logic [4:0]  wb_reg_o,
  input logic [31:0] wb_val_o,

  // DUT internals
  input logic [31:0] alu_r,
  input logic        control_load,
  input logic        control_store
);
  default clocking cb @(posedge clk_i); endclocking

  // Constant stall
  assert property (stall_o === 1'b0);

  // Reset clears sequential state on next cycle
  assert property (rst_i |=> alu_r==32'd0 && control_load==1'b0 && control_store==1'b0
                             && do_wb_o==1'b0 && wb_reg_o==5'd0);

  // Sequential capture (skip first cycle after reset)
  assert property ((!rst_i && !$past(rst_i)) |-> alu_r     == $past(alu_i));
  assert property ((!rst_i && !$past(rst_i)) |-> control_load  == $past(control_load_i));
  assert property ((!rst_i && !$past(rst_i)) |-> control_store == $past(control_store_i));
  assert property ((!rst_i && !$past(rst_i)) |-> do_wb_o   == $past(do_wb_i));
  assert property ((!rst_i && !$past(rst_i)) |-> wb_reg_o  == $past(wb_reg_i));

  // Combinational WB mux semantics (based on registered controls)
  assert property (control_load |-> (wb_val_o == 32'd99));
  assert property (control_store && !control_load |-> $isunknown(wb_val_o));
  assert property (!control_load && !control_store |-> (wb_val_o == alu_r));

  // Priority when both load and store asserted: load wins
  assert property (control_load && control_store |-> wb_val_o == 32'd99);

  // No X on outputs except explicitly for store case
  assert property (!rst_i && !(control_store && !control_load) |-> !$isunknown(wb_val_o));
  assert property (!rst_i |-> !$isunknown({do_wb_o, wb_reg_o, stall_o}));

  // Unused input should not affect outputs/state when other inputs are stable
  assert property (!rst_i && !$past(rst_i)
                   && $changed(control_take_branch_i)
                   && $stable({alu_i,control_load_i,control_store_i,do_wb_i,wb_reg_i})
                   |->
                   $stable({alu_r,control_load,control_store,do_wb_o,wb_reg_o,wb_val_o}));

  // Coverage
  cover property (rst_i ##1 !rst_i);                                     // reset release
  cover property (!control_load && !control_store && wb_val_o==alu_r);   // ALU path
  cover property (control_load && wb_val_o==32'd99);                      // load path
  cover property (control_store && !control_load && $isunknown(wb_val_o));// store path
  cover property (control_load && control_store && wb_val_o==32'd99);     // both asserted
  cover property ($changed(alu_i) ##1 alu_r==$past(alu_i));               // alu capture
  cover property ($changed(do_wb_i) ##1 do_wb_o==$past(do_wb_i));         // do_wb capture
  cover property ($changed(wb_reg_i) ##1 wb_reg_o==$past(wb_reg_i));      // wb_reg capture
endmodule

// Bind into the DUT
bind stage4_memory stage4_memory_sva u_stage4_memory_sva (
  .clk_i, .rst_i,
  .alu_i, .control_load_i, .control_store_i, .control_take_branch_i,
  .do_wb_i, .wb_reg_i, .stall_o,
  .do_wb_o, .wb_reg_o, .wb_val_o,
  .alu_r, .control_load, .control_store
);