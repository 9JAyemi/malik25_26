
module fpadd_altpriority_encoder_6e8 (
    input [3:0] data,
    output [1:0] q,
    output zero
);

    wire [0:0] wire_altpriority_encoder13_q;
    wire wire_altpriority_encoder13_zero;
    wire [1:0] q_temp;

    // Instantiate one instance of fpadd_altpriority_encoder_3e8
    fpadd_altpriority_encoder_3e8 altpriority_encoder13 (
        .data({data[2], data[1:0]}),
        .q(wire_altpriority_encoder13_q),
        .zero(wire_altpriority_encoder13_zero)
    );

    // Assign the outputs of the instance to the output of the overall module
    assign q_temp = wire_altpriority_encoder13_zero ? {1'b1, wire_altpriority_encoder13_q} : {1'b0, wire_altpriority_encoder13_q};
    assign q = data[3:0] == 4'b0000 ? q_temp : 2'b11;
    assign zero = (wire_altpriority_encoder13_zero) & (data[3:0] == 4'b0000);

endmodule
module fpadd_altpriority_encoder_3e8 (
    input [2:0] data,
    output [0:0] q,
    output zero
);

    wire [1:0] wire_priority_encoder3_data;
    wire [0:0] wire_priority_encoder3_q;
    wire wire_priority_encoder3_zero;

    // Instantiate one instance of fpadd_priority_encoder_2e8
    fpadd_priority_encoder_2e8 priority_encoder3 (
        .data(wire_priority_encoder3_data),
        .q(wire_priority_encoder3_q),
        .zero(wire_priority_encoder3_zero)
    );

    // Assign the outputs of the instance to the output of the overall module
    assign wire_priority_encoder3_data = {data[1], data[0]};
    assign q = wire_priority_encoder3_q;
    assign zero = wire_priority_encoder3_zero;

endmodule
module fpadd_priority_encoder_2e8 (
    input [1:0] data,
    output [0:0] q,
    output zero
);

    wire [0:0] wire_altpriority_encoder2_q;
    wire wire_altpriority_encoder2_zero;

    // Instantiate one instance of fpadd_altpriority_encoder_2e8
    fpadd_altpriority_encoder_2e8 altpriority_encoder2 (
        .data(data),
        .q(wire_altpriority_encoder2_q),
        .zero(wire_altpriority_encoder2_zero)
    );

    // Assign the outputs of the instance to the output of the overall module
    assign q = wire_altpriority_encoder2_q;
    assign zero = wire_altpriority_encoder2_zero;

endmodule
module fpadd_altpriority_encoder_2e8 (
    input [1:0] data,
    output [0:0] q,
    output zero
);

    wire [0:0] wire_altpriority_encoder1_q;

    // Instantiate one instance of fpadd_altpriority_encoder_1e8
    fpadd_altpriority_encoder_1e8 altpriority_encoder1 (
        .data(data[0:0]),
        .q(wire_altpriority_encoder1_q),
        .zero(zero)
    );

    // Assign the outputs of the instance to the output of the overall module
    assign q = wire_altpriority_encoder1_q;

endmodule
module fpadd_altpriority_encoder_1e8 (
    input [0:0] data,
    output [0:0] q,
    output zero
);

    // Assign the outputs of the instance to the output of the overall module
    assign q = data;
    assign zero = (data == 1'b0);

endmodule