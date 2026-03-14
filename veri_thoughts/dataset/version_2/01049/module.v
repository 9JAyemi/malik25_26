
module barrel_shifter (
    input [3:0] A,
    input [2:0] B,
    output [3:0] S,
    output C
);

    wire [3:0] temp;

    assign temp = B[2] ? A :
                  B[1] ? {A[2:0], 1'b0} :
                  B[0] ? {A[1:0], 2'b0} :
                          {A[0], 3'b0};

    assign S = temp;
    assign C = temp[0];

endmodule
