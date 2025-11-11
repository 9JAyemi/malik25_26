
module AXI_Master
(
    input axi_clk,
    input axi_rst,
    input [31:0] axi_araddr,
    input axi_arvalid,
    output axi_arready,
    output [31:0] axi_rdata,
    output axi_rvalid,
    input axi_rready,
    input [31:0] axi_awaddr,
    input axi_awvalid,
    output axi_awready,
    input [31:0] axi_wdata,
    input axi_wvalid,
    output axi_wready,
    output [1:0] axi_bresp,
    output axi_bvalid,
    input axi_bready
);

// Internal registers
reg [31:0] addr_reg;
reg [31:0] data_reg;
reg [1:0] resp_reg;
reg [1:0] state_reg;

// Constants
localparam IDLE = 2'b00;
localparam READ = 2'b01;
localparam WRITE = 2'b10;

// RTL Code

// Output logic
assign axi_arready = (state_reg == IDLE) ? 1'b1 : 1'b0;
assign axi_awready = (state_reg == IDLE) ? 1'b1 : 1'b0;
assign axi_wready = (state_reg == IDLE) ? 1'b1 : 1'b0;
assign axi_bresp = resp_reg;
assign axi_bvalid = (state_reg == WRITE) ? 1'b1 : 1'b0;
assign axi_rdata = (state_reg == READ) ? mem[addr_reg] : 32'h0;
assign axi_rvalid = (state_reg == READ) ? 1'b1 : 1'b0;

// State machine
always @(posedge axi_clk) begin
    if (axi_rst) begin
        state_reg <= IDLE;
        addr_reg <= 32'h00000000;
        data_reg <= 32'h00000000;
        resp_reg <= 2'b00;
    end else begin
        case (state_reg)
            IDLE: begin
                if (axi_arvalid) begin
                    state_reg <= READ;
                    addr_reg <= axi_araddr;
                end else if (axi_awvalid) begin
                    state_reg <= WRITE;
                    addr_reg <= axi_awaddr;
                    data_reg <= axi_wdata;
                end
            end
            READ: begin
                if (axi_rready) begin
                    resp_reg <= 2'b00;
                    state_reg <= IDLE;
                end
            end
            WRITE: begin
                if (axi_bready) begin
                    resp_reg <= 2'b00;
                    state_reg <= IDLE;
                end
            end
        endcase
    end
end

// Memory
reg [31:0] mem [0:1023];

endmodule