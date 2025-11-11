
module receiver #(
    parameter DATA_BITS = 32
)(
    input clk, rst, stb,
    input [DATA_BITS-1:0] data,  // Added the data input
    output [DATA_BITS-1:0] data_out,
    output ack, valid
);

    reg [DATA_BITS-1:0] data_reg;
    reg ack_reg, valid_reg;
    wire stb_selected;

    // Synchronizer for stb signal
    wire stb_sync;
    synchronizer_1bit sync1 (clk, rst, stb, stb_sync);
    assign stb_selected = stb_sync;

    // Latch data into register on stb signal assertion
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            data_reg <= 0;
        end else if (stb_selected) begin
            data_reg <= data;
        end
    end

    // Connect data_out to stored data value
    assign data_out = data_reg;

    // Acknowledge signal
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            ack_reg <= 1'b0;
        end else if (stb_selected) begin
            ack_reg <= 1'b1;
        end
    end
    assign ack = ack_reg;

    // Valid signal
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            valid_reg <= 1'b0;
        end else if (ack_reg) begin
            valid_reg <= 1'b1;
        end
    end
    assign valid = valid_reg;

endmodule
module synchronizer_1bit (
    input clk, rst, in,
    output out
);

    reg [1:0] sync_reg;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            sync_reg <= 2'b00;
        end else begin
            sync_reg <= {sync_reg[0], in};
        end
    end

    assign out = sync_reg[1];

endmodule