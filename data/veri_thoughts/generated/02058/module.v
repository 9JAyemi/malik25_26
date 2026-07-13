
module fpoint_qsys_addsub_single_altpriority_encoder_lha(
    input [3:0] data,
    output [1:0] q
);

    // Instantiate the nested modules

    fpoint_qsys_addsub_single_altpriority_encoder_iha iha_0(
        .data(data[1:0]),
        .q(q[0])
    );

    fpoint_qsys_addsub_single_altpriority_encoder_iha iha_1(
        .data(data[3:2]),
        .q(q[1])
    );

endmodule

module fpoint_qsys_addsub_single_altpriority_encoder_iha(
    input [1:0] data,
    output [0:0] q
);

    assign q = data[0] ? 1'b1 : data[1];

endmodule

module fpoint_qsys_addsub_single_altpriority_encoder_i0b(
    input [1:0] data,
    output [0:0] q,
    output zero
);

    assign q = data[0] ? 1'b1 : data[1];
    assign zero = (data[0] & data[1]);

endmodule
