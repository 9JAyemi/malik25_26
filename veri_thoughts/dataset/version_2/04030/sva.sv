module cpu_interface_sva (
    input logic clk,
    input logic reset_n,
    input logic reset_req,
    input logic [31:0] d_readdata,
    input logic d_waitrequest,
    input logic [31:0] i_readdata,
    input logic i_waitrequest,
    input logic [31:0] irq,
    input logic [8:0] debug_mem_slave_address,
    input logic [3:0] debug_mem_slave_byteenable,
    input logic debug_mem_slave_debugaccess,
    input logic debug_mem_slave_read,
    input logic debug_mem_slave_write,
    input logic [31:0] debug_mem_slave_writedata,
    input logic [28:0] d_address,
    input logic [3:0] d_byteenable,
    input logic d_read,
    input logic d_write,
    input logic [31:0] d_writedata,
    input logic debug_mem_slave_debugaccess_to_roms,
    input logic [28:0] i_address,
    input logic i_read,
    input logic debug_reset_request,
    input logic [31:0] debug_mem_slave_readdata,
    input logic debug_mem_slave_waitrequest,
    input logic dummy_ci_port
);

    // Data master constant outputs stay fixed.
    check_data_master_constants: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((d_address == 29'd0) &&
         (d_byteenable == 4'b1111) &&
         (d_writedata == 32'd0))
    );

    // Instruction address is tied low.
    check_instruction_address_constant: assert property (
        @(posedge clk) disable iff (!reset_n)
        (i_address == 29'd0)
    );

    // Debug and auxiliary outputs are tied low.
    check_debug_outputs_constant_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((debug_mem_slave_debugaccess_to_roms == 1'b0) &&
         (debug_reset_request == 1'b0) &&
         (debug_mem_slave_readdata == 32'd0) &&
         (debug_mem_slave_waitrequest == 1'b0) &&
         (dummy_ci_port == 1'b0))
    );

    // A reset cycle clears both read strobes.
    check_reset_clears_reads: assert property (
        @(posedge clk)
        (!reset_n) |=> ((d_read == 1'b0) && (i_read == 1'b0))
    );

    // A reset request clears both read strobes.
    check_reset_req_clears_reads: assert property (
        @(posedge clk) disable iff (!reset_n)
        reset_req |=> ((d_read == 1'b0) && (i_read == 1'b0))
    );

    // Data waitrequest deasserts both data strobes.
    check_d_waitrequest_deasserts_data_access: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!reset_req && d_waitrequest) |=> ((d_read == 1'b0) && (d_write == 1'b0))
    );

    // With no data waitrequest, read asserts and write stays low.
    check_d_ready_asserts_read_only: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!reset_req && !d_waitrequest) |=> ((d_read == 1'b1) && (d_write == 1'b0))
    );

    // Instruction waitrequest deasserts the instruction read.
    check_i_waitrequest_deasserts_read: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!reset_req && i_waitrequest) |=> (i_read == 1'b0)
    );

    // With no instruction waitrequest, instruction read asserts.
    check_i_ready_asserts_read: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!reset_req && !i_waitrequest) |=> (i_read == 1'b1)
    );

endmodule