module forward_unit_sva
#(
    parameter DATA_WIDTH = 32,
    parameter REG_ADDR_WIDTH = 5
)
(
    input logic clk,
    input logic [DATA_WIDTH-1:0] data_alu_a_in,
    input logic [DATA_WIDTH-1:0] data_alu_b_in,
    input logic [REG_ADDR_WIDTH-1:0] addr_alu_a_in,
    input logic [REG_ADDR_WIDTH-1:0] addr_alu_b_in,
    input logic [DATA_WIDTH-1:0] ex_mem_reg_a_data_in,
    input logic [DATA_WIDTH-1:0] ex_mem_reg_b_data_in,
    input logic [REG_ADDR_WIDTH-1:0] ex_mem_reg_a_addr_in,
    input logic [REG_ADDR_WIDTH-1:0] ex_mem_reg_b_addr_in,
    input logic ex_mem_reg_a_wr_ena_in,
    input logic ex_mem_reg_b_wr_ena_in,
    input logic [DATA_WIDTH-1:0] wb_reg_a_data_in,
    input logic [DATA_WIDTH-1:0] wb_reg_b_data_in,
    input logic [REG_ADDR_WIDTH-1:0] wb_reg_a_addr_in,
    input logic [REG_ADDR_WIDTH-1:0] wb_reg_b_addr_in,
    input logic wb_reg_a_wr_ena_in,
    input logic wb_reg_b_wr_ena_in,
    input logic [DATA_WIDTH-1:0] alu_a_mux_sel_out,
    input logic [DATA_WIDTH-1:0] alu_b_mux_sel_out
);

    // ALU A selects EX/MEM reg A on the highest-priority match.
    check_alu_a_sel_ex_mem_a: assert property (
        @(posedge clk)
        ((addr_alu_a_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in)
        |-> (alu_a_mux_sel_out == ex_mem_reg_a_data_in)
    );

    // ALU A selects EX/MEM reg B when reg A is not selected.
    check_alu_a_sel_ex_mem_b: assert property (
        @(posedge clk)
        (!((addr_alu_a_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         ((addr_alu_a_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in))
        |-> (alu_a_mux_sel_out == ex_mem_reg_b_data_in)
    );

    // ALU A selects WB reg A when EX/MEM paths are not selected.
    check_alu_a_sel_wb_a: assert property (
        @(posedge clk)
        (!((addr_alu_a_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_a_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         ((addr_alu_a_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in))
        |-> (alu_a_mux_sel_out == wb_reg_a_data_in)
    );

    // ALU A selects WB reg B when higher-priority paths are not selected.
    check_alu_a_sel_wb_b: assert property (
        @(posedge clk)
        (!((addr_alu_a_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_a_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         !((addr_alu_a_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in) &&
         ((addr_alu_a_in == wb_reg_b_addr_in) & wb_reg_b_wr_ena_in))
        |-> (alu_a_mux_sel_out == wb_reg_b_data_in)
    );

    // ALU A passes through its input when no forwarding condition matches.
    check_alu_a_sel_default: assert property (
        @(posedge clk)
        (!((addr_alu_a_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_a_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         !((addr_alu_a_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in) &&
         !((addr_alu_a_in == wb_reg_b_addr_in) & wb_reg_b_wr_ena_in))
        |-> (alu_a_mux_sel_out == data_alu_a_in)
    );

    // ALU B selects EX/MEM reg A on the highest-priority match.
    check_alu_b_sel_ex_mem_a: assert property (
        @(posedge clk)
        ((addr_alu_b_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in)
        |-> (alu_b_mux_sel_out == ex_mem_reg_a_data_in)
    );

    // ALU B selects EX/MEM reg B when reg A is not selected.
    check_alu_b_sel_ex_mem_b: assert property (
        @(posedge clk)
        (!((addr_alu_b_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         ((addr_alu_b_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in))
        |-> (alu_b_mux_sel_out == ex_mem_reg_b_data_in)
    );

    // ALU B selects WB reg A when EX/MEM paths are not selected.
    check_alu_b_sel_wb_a: assert property (
        @(posedge clk)
        (!((addr_alu_b_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_b_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         ((addr_alu_b_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in))
        |-> (alu_b_mux_sel_out == wb_reg_a_data_in)
    );

    // ALU B selects WB reg B when higher-priority paths are not selected.
    check_alu_b_sel_wb_b: assert property (
        @(posedge clk)
        (!((addr_alu_b_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_b_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         !((addr_alu_b_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in) &&
         ((addr_alu_b_in == wb_reg_b_addr_in) & wb_reg_b_wr_ena_in))
        |-> (alu_b_mux_sel_out == wb_reg_b_data_in)
    );

    // ALU B passes through its input when no forwarding condition matches.
    check_alu_b_sel_default: assert property (
        @(posedge clk)
        (!((addr_alu_b_in == ex_mem_reg_a_addr_in) & ex_mem_reg_a_wr_ena_in) &&
         !((addr_alu_b_in == ex_mem_reg_b_addr_in) & ex_mem_reg_b_wr_ena_in) &&
         !((addr_alu_b_in == wb_reg_a_addr_in) & wb_reg_a_wr_ena_in) &&
         !((addr_alu_b_in == wb_reg_b_addr_in) & wb_reg_b_wr_ena_in))
        |-> (alu_b_mux_sel_out == data_alu_b_in)
    );

endmodule