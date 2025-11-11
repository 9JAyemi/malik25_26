// SVA for wb_pipe_reg: concise, high-quality checks and coverage.
// Bind this module to the DUT to monitor behavior.

module wb_pipe_reg_sva (
  input  wire        clk,
  input  wire        reset,
  input  wire        valid_wb_pipe_reg_i,
  input  wire        rf_en_wb_pipe_reg_i,
  input  wire [1:0]  wb_sel_wb_pipe_reg_i,
  input  wire [4:0]  rd_wb_pipe_reg_i,
  input  wire [31:0] alu_res_wb_pipe_reg_i,
  input  wire [31:0] read_data_wb_pipe_reg_i,
  input  wire [31:0] next_seq_pc_wb_pipe_reg_i,
  input  wire        instr_retired_wb_pipe_reg_o,
  input  wire        rf_en_wb_pipe_reg_o,
  input  wire [1:0]  wb_sel_wb_pipe_reg_o,
  input  wire [4:0]  rd_wb_pipe_reg_o,
  input  wire [31:0] alu_res_wb_pipe_reg_o,
  input  wire [31:0] read_data_wb_pipe_reg_o,
  input  wire [31:0] next_seq_pc_wb_pipe_reg_o
);

  // Default clock/reset for synchronous checks
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // 1) One-cycle capture: outputs reflect previous-cycle inputs (when prior cycle not in reset)
  property p_capture_1cycle;
    !$past(reset) |-> (
      rf_en_wb_pipe_reg_o         == $past(rf_en_wb_pipe_reg_i)   &&
      wb_sel_wb_pipe_reg_o        == $past(wb_sel_wb_pipe_reg_i)  &&
      rd_wb_pipe_reg_o            == $past(rd_wb_pipe_reg_i)      &&
      alu_res_wb_pipe_reg_o       == $past(alu_res_wb_pipe_reg_i) &&
      read_data_wb_pipe_reg_o     == $past(read_data_wb_pipe_reg_i) &&
      next_seq_pc_wb_pipe_reg_o   == $past(next_seq_pc_wb_pipe_reg_i) &&
      instr_retired_wb_pipe_reg_o == $past(valid_wb_pipe_reg_i)
    );
  endproperty
  assert property (p_capture_1cycle);

  // 2) Stability: if inputs are stable, outputs remain stable
  property p_stable;
    !$past(reset) &&
    $stable({ rf_en_wb_pipe_reg_i, wb_sel_wb_pipe_reg_i, rd_wb_pipe_reg_i,
              alu_res_wb_pipe_reg_i, read_data_wb_pipe_reg_i, next_seq_pc_wb_pipe_reg_i,
              valid_wb_pipe_reg_i })
    |-> $stable({ rf_en_wb_pipe_reg_o, wb_sel_wb_pipe_reg_o, rd_wb_pipe_reg_o,
                  alu_res_wb_pipe_reg_o, read_data_wb_pipe_reg_o, next_seq_pc_wb_pipe_reg_o,
                  instr_retired_wb_pipe_reg_o });
  endproperty
  assert property (p_stable);

  // 3) No X/Z on outputs when out of reset
  assert property (!reset |-> ! $isunknown({
    rf_en_wb_pipe_reg_o, wb_sel_wb_pipe_reg_o, rd_wb_pipe_reg_o,
    alu_res_wb_pipe_reg_o, read_data_wb_pipe_reg_o, next_seq_pc_wb_pipe_reg_o,
    instr_retired_wb_pipe_reg_o
  }));

  // 4) Reset behavior: immediate and continuous zeroing during reset
  // Immediate on async reset edge
  assert property (@(posedge reset)
    rf_en_wb_pipe_reg_o==0 && wb_sel_wb_pipe_reg_o==0 && rd_wb_pipe_reg_o==0 &&
    alu_res_wb_pipe_reg_o==0 && read_data_wb_pipe_reg_o==0 &&
    next_seq_pc_wb_pipe_reg_o==0 && instr_retired_wb_pipe_reg_o==0);

  // While reset is held high at clock edges
  assert property (@(posedge clk) reset |-> (
    rf_en_wb_pipe_reg_o==0 && wb_sel_wb_pipe_reg_o==0 && rd_wb_pipe_reg_o==0 &&
    alu_res_wb_pipe_reg_o==0 && read_data_wb_pipe_reg_o==0 &&
    next_seq_pc_wb_pipe_reg_o==0 && instr_retired_wb_pipe_reg_o==0));

  // 5) Functional coverage
  // Reset pulse observed
  cover property (@(posedge clk) $fell(reset));
  // Retirement observed
  cover property (@(posedge clk) !reset ##1 $rose(instr_retired_wb_pipe_reg_o));
  // All wb_sel values observed at output
  cover property (@(posedge clk) !reset && wb_sel_wb_pipe_reg_o==2'b00);
  cover property (@(posedge clk) !reset && wb_sel_wb_pipe_reg_o==2'b01);
  cover property (@(posedge clk) !reset && wb_sel_wb_pipe_reg_o==2'b10);
  cover property (@(posedge clk) !reset && wb_sel_wb_pipe_reg_o==2'b11);
  // rf_en toggles
  cover property (@(posedge clk) !reset ##1 $rose(rf_en_wb_pipe_reg_o));
  cover property (@(posedge clk) !reset ##1 $fell(rf_en_wb_pipe_reg_o));
  // rd covers zero and non-zero destinations
  cover property (@(posedge clk) !reset && rd_wb_pipe_reg_o==5'd0);
  cover property (@(posedge clk) !reset && rd_wb_pipe_reg_o!=5'd0);

endmodule

// Bind into the DUT
bind wb_pipe_reg wb_pipe_reg_sva wb_pipe_reg_sva_i (.*);