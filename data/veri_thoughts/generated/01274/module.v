
module barrel_shifter (
    input [3:0] A,
    input [1:0] S,
    output [3:0] B
);

    reg [3:0] temp;

    always @(*) begin
        temp = (S[1]) ? {A[3], A[3]} : // right shift
                       {A[1:0], A[3:2]}; // left shift
    end

    assign B = (S[0]) ? temp >> 1 : temp; // shift by 1 if S[0] is 1

endmodule