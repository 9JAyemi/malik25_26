module binary_storage_shift(
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] d,
    input [1:0] shift_ctrl,
    output reg [7:0] q,
    output reg [7:0] q_shifted // Shifted output
);

reg [3:0] flip_flop; // 4 D flip-flops
reg [7:0] shifted_d; // Shifted input
wire [1:0] shift_amt; // Shift amount

assign shift_amt = (shift_ctrl == 2'b00) ? 2'b00 :
                   (shift_ctrl == 2'b01) ? 2'b01 :
                   (shift_ctrl == 2'b10) ? 2'b10 :
                   2'b11;

always @ (posedge clk) begin
    if (reset) begin
        q <= 8'b0;
        q_shifted <= 8'b0;
        flip_flop <= 4'b0;
    end else begin
        flip_flop <= {flip_flop[2:0], d[7]};
        q <= {flip_flop[3], flip_flop[2], flip_flop[1], flip_flop[0]};
        shifted_d <= {d[5:0], 2'b00};
        q_shifted <= shifted_d << shift_amt;
    end
end

endmodule