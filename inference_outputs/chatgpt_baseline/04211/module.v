
module barrel_shifter (
    input [15:0] in,
    input [3:0] shift_amt,
    input shift_left,
    output reg [15:0] out
);

    always @(*) begin
        if (shift_left) begin
            out = in << shift_amt;
        end else begin
            out = in >> shift_amt;
        end
    end

endmodule