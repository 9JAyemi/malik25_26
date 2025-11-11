module barrel_shifter (
    input [3:0] A,
    input [1:0] shift_amount,
    input shift_dir,
    output [3:0] Y
);

    reg [3:0] shifted;

    always @(*) begin
        if (shift_dir) // left shift
            shifted = {A[shift_amount[1:0]-1:0], 4'b0};
        else // right shift
            shifted = {4'b0, A[3:shift_amount]};
    end

    assign Y = shifted;

endmodule