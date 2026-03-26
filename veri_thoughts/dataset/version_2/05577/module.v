module float_add_sub_altpriority_encoder_v28
    ( 
    input   [7:0]  data,
    output   [2:0]  q
    );

    wire  [1:0]   wire_altpriority_encoder31_q;
    wire  wire_altpriority_encoder31_zero;
    wire  [1:0]   wire_altpriority_encoder32_q;

    float_add_sub_altpriority_encoder_qh8   altpriority_encoder31
    ( 
        .data(data[3:0]),
        .q(wire_altpriority_encoder31_q),
        .zero(wire_altpriority_encoder31_zero)
    );

    float_add_sub_altpriority_encoder_q28   altpriority_encoder32
    ( 
        .data(data[7:4]),
        .q(wire_altpriority_encoder32_q)
    );

    assign q = {wire_altpriority_encoder31_zero, (({2{wire_altpriority_encoder31_zero}} & wire_altpriority_encoder32_q) | ({2{(~ wire_altpriority_encoder31_zero)}} & wire_altpriority_encoder31_q))};

endmodule

module float_add_sub_altpriority_encoder_qh8
    ( 
    input   [3:0]  data,
    output   [1:0]  q,
    output  zero
    );

    assign zero = (data[0] == 0) & (data[1] == 0) & (data[2] == 0) & (data[3] == 0);

    assign q[0] = data[0] | data[1];
    assign q[1] = data[2] | data[3];

endmodule

module float_add_sub_altpriority_encoder_q28
    ( 
    input   [3:0]  data,
    output   [1:0]  q
    );

    assign q[0] = data[0] | data[1];
    assign q[1] = data[2] | data[3];

endmodule