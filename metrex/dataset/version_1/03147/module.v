
module fifo_generator(
    input s_axi_aclk,
    input Rst0,
    input E,
    input [0:0]DIA,
    input [3:0]D,
    input fifo_tx_en,
    output [3:0]Q,
    output out,
    output txfifo_empty
);

// Register and wire declarations
reg [3:0] mem [0:7];
reg [2:0] wr_ptr;
reg [2:0] rd_ptr;
reg [2:0] next_wr_ptr;
reg [2:0] next_rd_ptr;
reg [3:0] next_wr_data;
wire [3:0] rd_data;
reg empty;
reg [2:0] count;
reg [2:0] next_count;
reg [1:0] wr_enable;
reg [1:0] rd_enable;

// Counter logic
always @(posedge s_axi_aclk) begin
    if (Rst0) begin
        count <= 0;
    end else begin
        count <= next_count;
    end
end

always @(*) begin
    if (count == 0) begin
        empty <= 1'b1;
    end else begin
        empty <= 1'b0;
    end
end

always @(*) begin
    next_count = count;
    if (wr_enable[0]) begin
        next_count = count + 1;
    end
    if (rd_enable[0]) begin
        next_count = count - 1;
    end
end

// Write pointer logic
always @(posedge s_axi_aclk) begin
    if (Rst0) begin
        wr_ptr <= 0;
    end else begin
        wr_ptr <= next_wr_ptr;
    end
end

always @(*) begin
    next_wr_data = {DIA, D};
    next_wr_ptr = wr_ptr;
    wr_enable = 0;
    if (E) begin
        wr_enable[0] = 1;
        next_wr_ptr = wr_ptr + 1;
        if (wr_ptr == 7) begin
            next_wr_ptr = 0;
        end
    end
end

// Read pointer logic
always @(posedge s_axi_aclk) begin
    if (Rst0) begin
        rd_ptr <= 0;
    end else begin
        rd_ptr <= next_rd_ptr;
    end
end

always @(*) begin
    rd_enable = 0;
    if (fifo_tx_en && !empty) begin
        rd_enable[0] = 1;
        next_rd_ptr = rd_ptr + 1;
        if (rd_ptr == 7) begin
            next_rd_ptr = 0;
        end
    end
end

// Data memory
always @(posedge s_axi_aclk) begin
    if (wr_enable[0]) begin
        mem[wr_ptr] <= next_wr_data;
    end
end

// Output logic
assign rd_data = mem[rd_ptr];
assign Q = rd_data;
assign out = empty;
assign txfifo_empty = empty && !wr_enable[0];

endmodule