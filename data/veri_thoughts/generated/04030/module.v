
module cpu_interface(
    input wire clk,
    input wire reset_n,
    input wire reset_req,
    input wire [31:0] d_readdata,
    input wire d_waitrequest,
    input wire [31:0] i_readdata,
    input wire i_waitrequest,
    input wire [31:0] irq,
    input wire [8:0] debug_mem_slave_address,
    input wire [3:0] debug_mem_slave_byteenable,
    input wire debug_mem_slave_debugaccess,
    input wire debug_mem_slave_read,
    input wire debug_mem_slave_write,
    input wire [31:0] debug_mem_slave_writedata,
    output wire [28:0] d_address,
    output wire [3:0] d_byteenable,
    output reg d_read,
    output reg d_write,
    output wire [31:0] d_writedata,
    output wire debug_mem_slave_debugaccess_to_roms,
    output wire [28:0] i_address,
    output reg i_read,
    output wire debug_reset_request,
    output wire [31:0] debug_mem_slave_readdata,
    output wire debug_mem_slave_waitrequest,
    output wire dummy_ci_port
);

    // Data master
    assign d_address = 29'd0;
    assign d_byteenable = 4'b1111;
    assign d_writedata = 32'd0;

    // Instruction master
    assign i_address = 29'd0;

    // Debug memory slave
    assign debug_mem_slave_debugaccess_to_roms = 1'b0;
    assign debug_reset_request = 1'b0;
    assign debug_mem_slave_readdata = 32'd0;
    assign debug_mem_slave_waitrequest = 1'b0;
    assign dummy_ci_port = 1'b0;

    // Handle signals
    always @(posedge clk) begin
        if (!reset_n) begin
            d_read <= 1'b0;
            i_read <= 1'b0;
        end else begin
            if (reset_req) begin
                d_read <= 1'b0;
                i_read <= 1'b0;
            end else begin
                if (d_waitrequest) begin
                    d_read <= 1'b0;
                    d_write <= 1'b0;
                end else begin
                    d_read <= 1'b1;
                    d_write <= 1'b0;
                end
                if (i_waitrequest) begin
                    i_read <= 1'b0;
                end else begin
                    i_read <= 1'b1;
                end
            end
        end
    end

endmodule