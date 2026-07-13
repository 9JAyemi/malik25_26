module write_back_sva
#(
   parameter DATA_WIDTH = 32,
   parameter REG_ADDR_WIDTH = 5
)
(
   input  logic                       clk,

   input  logic [DATA_WIDTH-1:0]      mem_data_in,
   input  logic [DATA_WIDTH-1:0]      alu_data_in,
   input  logic [DATA_WIDTH-1:0]      hi_data_in,
   input  logic [REG_ADDR_WIDTH-1:0]  reg_a_wr_addr_in,
   input  logic [REG_ADDR_WIDTH-1:0]  reg_b_wr_addr_in,
   input  logic                       reg_a_wr_en_in,
   input  logic                       reg_b_wr_en_in,
   input  logic                       write_back_mux_sel,

   input  logic [REG_ADDR_WIDTH-1:0]  reg_a_wr_addr_out,
   input  logic [REG_ADDR_WIDTH-1:0]  reg_b_wr_addr_out,
   input  logic [DATA_WIDTH-1:0]      reg_a_wr_data_out,
   input  logic [DATA_WIDTH-1:0]      reg_b_wr_data_out,
   input  logic                       reg_a_wr_en_out,
   input  logic                       reg_b_wr_en_out
);

    ///// Combinational passthrough/mux behavior /////
    // reg_a_wr_data_out equals selected input per write_back_mux_sel.
    check_a_data_mux: assert property (
        @(posedge clk) reg_a_wr_data_out == (write_back_mux_sel ? mem_data_in : alu_data_in)
    );

    // When sel=1, reg_a_wr_data_out equals mem_data_in.
    check_a_data_when_sel1: assert property (
        @(posedge clk) (write_back_mux_sel == 1'b1) |-> (reg_a_wr_data_out == mem_data_in)
    );

    // When sel=0, reg_a_wr_data_out equals alu_data_in.
    check_a_data_when_sel0: assert property (
        @(posedge clk) (write_back_mux_sel == 1'b0) |-> (reg_a_wr_data_out == alu_data_in)
    );

    // reg_b_wr_data_out passes through hi_data_in.
    check_b_data_passthrough: assert property (
        @(posedge clk) reg_b_wr_data_out == hi_data_in
    );

    // reg_a_wr_en_out passes through reg_a_wr_en_in.
    check_a_wr_en_passthrough: assert property (
        @(posedge clk) reg_a_wr_en_out == reg_a_wr_en_in
    );

    // reg_b_wr_en_out passes through reg_b_wr_en_in.
    check_b_wr_en_passthrough: assert property (
        @(posedge clk) reg_b_wr_en_out == reg_b_wr_en_in
    );

    // reg_a_wr_addr_out passes through reg_a_wr_addr_in.
    check_a_addr_passthrough: assert property (
        @(posedge clk) reg_a_wr_addr_out == reg_a_wr_addr_in
    );

    // reg_b_wr_addr_out passes through reg_b_wr_addr_in.
    check_b_addr_passthrough: assert property (
        @(posedge clk) reg_b_wr_addr_out == reg_b_wr_addr_in
    );

endmodule