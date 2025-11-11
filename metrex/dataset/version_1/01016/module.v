module adder_shifter (
    input [7:0] A,
    input [7:0] B,
    input carry_in,
    input sub,
    input [1:0] shift_amount,
    input shift_direction,
    output reg [7:0] sum,
    output reg borrow_out,
    output reg [7:0] shifted_output
);

reg [8:0] temp_sum;
reg [7:0] temp_shifted_output;

always @(*) begin
    if (sub) begin
        temp_sum = {A, 1'b0} - {B, 1'b0} - carry_in;
        borrow_out = temp_sum[8];
    end else begin
        temp_sum = {A, 1'b0} + {B, 1'b0} + carry_in;
        borrow_out = temp_sum[8];
    end
end

always @(*) begin
    case (shift_direction)
        2'b00: temp_shifted_output = temp_sum << shift_amount;
        2'b01: temp_shifted_output = temp_sum >> shift_amount;
        default: temp_shifted_output = 8'b0;
    endcase
end

always @(*) begin
    sum <= temp_sum[7:0];
    shifted_output <= temp_shifted_output;
end

endmodule