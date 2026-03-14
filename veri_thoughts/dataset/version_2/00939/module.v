
module adder_4bit (
    aclr,
    clock,
    A,
    B,
    CIN,
    S,
    COUT
);

    input aclr;
    input clock;
    input [3:0] A;
    input [3:0] B;
    input CIN;
    output [3:0] S;
    output COUT;

    wire [3:0] sum;
    wire [3:0] carry;

    // Instantiate full adders
    full_adder U0_fa0 (
        .A(A[0]),
        .B(B[0]),
        .CIN(CIN),
        .SUM(sum[0]),
        .COUT(carry[0])
    );
    full_adder U1_fa1 (
        .A(A[1]),
        .B(B[1]),
        .CIN(carry[0]),
        .SUM(sum[1]),
        .COUT(carry[1])
    );
    full_adder U2_fa2 (
        .A(A[2]),
        .B(B[2]),
        .CIN(carry[1]),
        .SUM(sum[2]),
        .COUT(carry[2])
    );
    full_adder U3_fa3 (
        .A(A[3]),
        .B(B[3]),
        .CIN(carry[2]),
        .SUM(sum[3]),
        .COUT(COUT)
    );

    // Instantiate registers
    reg [3:0] S_reg;
    always @(posedge clock or negedge aclr) begin
        if (!aclr) begin
            S_reg <= 4'b0;
        end else if (COUT) begin
            S_reg <= sum;
        end
    end

    assign S = S_reg;

endmodule
module full_adder (
    A,
    B,
    CIN,
    SUM,
    COUT
);

    input A;
    input B;
    input CIN;
    output SUM;
    output COUT;

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (B & CIN) | (CIN & A);

endmodule