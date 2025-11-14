
module counter (
    input CLK,
    input RESET,
    input LOAD,
    input [3:0] LOAD_VAL,
    output [3:0] Q
);
    reg [3:0] Q;

    always @(posedge CLK, posedge RESET) begin
        if (RESET) begin
            Q <= 4'b0;
        end else if (LOAD) begin
            Q <= LOAD_VAL;
        end else begin
            Q <= Q + 1;
        end
    end
endmodule
module priority_mux (
    input [3:0] A, B, C, D,
    input [1:0] S,
    output Y, Z
);
    wire Y, Z;

    assign Y = (S == 2'b01) ? A :
              (S == 2'b10) ? B :
              (S == 2'b11) ? ((D) ? D : (C) ? C : (B) ? B : A) :
              1'b0;

    assign Z = (S == 2'b01) ? ~A :
              (S == 2'b10) ? ~B :
              (S == 2'b11) ? ((D) ? ~D : (C) ? ~C : (B) ? ~B : ~A) :
              1'b0;
endmodule
module final_output_module (
    input [3:0] Q,
    input Y,
    output final_output
);
    wire final_output;

    assign final_output = (Q[0] == 1) && Y;
endmodule
module top_module (
    input CLK,
    input RESET,
    input LOAD,
    input [3:0] LOAD_VAL,
    input [3:0] A, B, C, D,
    input [1:0] S,
    output [3:0] Q,
    output Y, Z,
    output final_output
);
    counter counter_inst (
        .CLK(CLK),
        .RESET(RESET),
        .LOAD(LOAD),
        .LOAD_VAL(LOAD_VAL),
        .Q(Q)
    );

    priority_mux priority_mux_inst (
        .A(A),
        .B(B),
        .C(C),
        .D(D),
        .S(S),
        .Y(Y),
        .Z(Z)
    );

    final_output_module final_output_inst (
        .Q(Q),
        .Y(Y),
        .final_output(final_output)
    );
endmodule