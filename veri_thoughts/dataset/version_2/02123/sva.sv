module cpu_mem_sva (
    input logic rst,
    input logic clk,
    input logic cpu_stall,
    input logic ex_c_rfw,
    input logic [1:0] ex_c_wbsource,
    input logic [1:0] ex_c_drw,
    input logic [31:0] ex_alu_r,
    input logic [31:0] ex_rfb,
    input logic [4:0] ex_rf_waddr,
    input logic [31:0] ex_jalra,
    input logic [4:0] ex_rt,
    input logic [31:0] wb_wdata,
    input logic p_c_rfw,
    input logic [1:0] p_c_wbsource,
    input logic [31:0] p_alu_r,
    input logic [31:0] dmem_data,
    input logic [4:0] p_rf_waddr,
    input logic [31:0] p_jalra,
    input logic [31:0] dmem_addr,
    input logic [1:0] dmem_drw,
    input logic [31:0] dmem_in,
    input logic [31:0] p_dout
);

    ///// Reset and stall behavior /////
    // On !cpu_stall and rst, all pipeline registers clear to 0 on next cycle.
    reset_clears_regs: assert property (
        @(posedge clk) (!cpu_stall && rst) |=> (p_c_rfw == 1'b0) && (p_c_wbsource == 2'b00) &&
                                           (p_alu_r == 32'b0) && (p_rf_waddr == 5'b0) &&
                                           (p_jalra == 32'b0) && (p_dout == 32'b0)
    );

    // When cpu_stall is asserted, all pipeline registers hold their value.
    hold_regs_on_stall: assert property (
        @(posedge clk) disable iff (rst) cpu_stall |=> $stable({p_c_rfw, p_c_wbsource, p_alu_r, p_rf_waddr, p_jalra, p_dout})
    );

    ///// Register captures when enabled (!cpu_stall and !rst) /////
    // p_c_rfw captures ex_c_rfw on next cycle.
    capture_p_c_rfw: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_c_rfw == $past(ex_c_rfw))
    );

    // p_c_wbsource captures ex_c_wbsource on next cycle.
    capture_p_c_wbsource: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_c_wbsource == $past(ex_c_wbsource))
    );

    // p_alu_r captures ex_alu_r on next cycle.
    capture_p_alu_r: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_alu_r == $past(ex_alu_r))
    );

    // p_rf_waddr captures ex_rf_waddr on next cycle.
    capture_p_rf_waddr: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_rf_waddr == $past(ex_rf_waddr))
    );

    // p_jalra captures ex_jalra on next cycle.
    capture_p_jalra: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_jalra == $past(ex_jalra))
    );

    // p_dout captures dmem_in on next cycle.
    capture_p_dout: assert property (
        @(posedge clk) disable iff (rst) (!cpu_stall) |=> (p_dout == $past(dmem_in))
    );

    ///// Combinational pass-throughs /////
    // dmem_addr is a pure pass-through of ex_alu_r.
    comb_dmem_addr_passthrough: assert property (
        @(posedge clk) disable iff (rst) dmem_addr == ex_alu_r
    );

    // dmem_drw is a pure pass-through of ex_c_drw.
    comb_dmem_drw_passthrough: assert property (
        @(posedge clk) disable iff (rst) dmem_drw == ex_c_drw
    );

    // dmem_data selects wb_wdata when forward, else ex_rfb.
    comb_dmem_data_forward_mux: assert property (
        @(posedge clk) disable iff (rst)
            dmem_data == ((p_c_rfw && (ex_rt == p_rf_waddr) && (p_rf_waddr != 5'd0)) ? wb_wdata : ex_rfb)
    );

endmodule