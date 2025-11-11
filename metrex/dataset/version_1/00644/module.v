
module fp_convert_altpriority_encoder_3v7 (
    input [2:0] data,
    output reg [1:0] q
);

    wire q0;
    wire q1;
    wire q2;
    wire q3;

    assign q0 = ~|data;
    assign q1 = ~|data[2:1];
    assign q2 = ~|data[2:0];
    assign q3 = ~|data[2:1];

    always @* begin
        q[0] <= (~q0 & ~q1 & q2) | (~q0 & q1 & q3) | (q0 & ~q1 & q3) | (q0 & q1 & q2);
        q[1] <= (~q0 & q1 & q2) | (q0 & ~q1 & q2) | (q0 & q1 & q3) | (q0 & ~q1 & q3);
    end

endmodule
module fp_convert_altpriority_encoder_3e8 (
    input [2:0] data,
    output reg [1:0] q,
    output reg zero
);

    wire [1:0] q0;
    wire [1:0] q1;
    wire [1:0] q2;
    wire [1:0] q3;

    fp_convert_altpriority_encoder_3v7 encoder0(
        .data(data),
        .q(q0)
    );

    fp_convert_altpriority_encoder_3v7 encoder1(
        .data({data[1:0], data[2]}),
        .q(q1)
    );

    fp_convert_altpriority_encoder_3v7 encoder2(
        .data({data[0], data[2:1]}),
        .q(q2)
    );

    fp_convert_altpriority_encoder_3v7 encoder3(
        .data(data[2:0]),
        .q(q3)
    );

    always @* begin
        zero <= ~(|data);
        q[0] <= (~zero & q2[1]) | (zero & q0[1]);
        q[1] <= (~zero & q1[1]) | (zero & q3[1]);
    end

endmodule
module fp_convert_altpriority_encoder_6v7 (
    input [3:0] data,
    output reg [2:0] q
);

    wire [1:0] wire_altpriority_encoder21_q;
    wire [1:0] wire_altpriority_encoder22_q;

    fp_convert_altpriority_encoder_3v7 altpriority_encoder21(
        .data({data[2:1], data[0]}),
        .q(wire_altpriority_encoder21_q)
    );

    fp_convert_altpriority_encoder_3e8 altpriority_encoder22(
        .data(data[3:1]),
        .q(wire_altpriority_encoder22_q),
        .zero()
    );

    always @* begin
        q <= {(~wire_altpriority_encoder22_q[1]), (wire_altpriority_encoder22_q[1] & wire_altpriority_encoder21_q[1]) | (~wire_altpriority_encoder22_q[1] & wire_altpriority_encoder22_q[0])};
    end

endmodule