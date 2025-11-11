
module fifo(
    input clk,
    input wr,
    input [7:0] din,
    output reg rd,
    output reg [7:0] dout
);

reg [7:0] mem [0:7]; // Memory for storing FIFO elements
reg [2:0] wr_ptr = 3'b000; // Write pointer
reg [2:0] rd_ptr = 3'b000; // Read pointer

// Write logic
always @(posedge clk) begin
    if (wr) begin // Write only if wr=1
        mem[wr_ptr] <= din;
        wr_ptr <= wr_ptr + 3'b001;
        if (wr_ptr == 3'b100) begin
            wr_ptr <= 3'b000;
        end
    end
end

// Read logic
always @(posedge clk) begin
    if (rd) begin // Read only if rd=1
        dout <= mem[rd_ptr];
        rd_ptr <= rd_ptr + 3'b001;
        if (rd_ptr == 3'b100) begin
            rd_ptr <= 3'b000;
        end
    end
end

// Output logic
always @(*) begin
    rd = (rd_ptr != wr_ptr);
end

endmodule