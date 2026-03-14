
module position_module (
    input wire [2:0] vec,
    output wire pos0,
    output wire pos1,
    output wire pos2
);

    assign pos0 = (vec == 3'b000);
    assign pos1 = (vec == 3'b001);
    assign pos2 = (vec == 3'b010);

endmodule
module full_adder (
    input wire a,
    input wire b,
    input wire cin,
    output wire sum,
    output wire cout
);

    assign {cout, sum} = a + b + cin;

endmodule
module functional_module (
    input wire pos0,
    input wire pos1,
    input wire pos2,
    input wire sum,
    output wire [3:0] outv
);

    assign outv = {pos2, pos1, pos0, sum};

endmodule
module control_logic (
    input wire select,
    output wire pos0_en,
    output wire pos1_en,
    output wire pos2_en,
    output wire sum_en
);

    assign pos0_en = (select) ? 1'b0 : 1'b1;
    assign pos1_en = (select) ? 1'b0 : 1'b1;
    assign pos2_en = (select) ? 1'b0 : 1'b1;
    assign sum_en = (!select) ? 1'b0 : 1'b1;

endmodule
module top_module (
    input wire [2:0] vec,
    input wire a, b, cin,
    input wire select,
    output wire cout,
    output wire [3:0] outv
);

    wire pos0, pos1, pos2, sum;
    wire pos0_en, pos1_en, pos2_en, sum_en;

    position_module pos_mod(
        .vec(vec),
        .pos0(pos0),
        .pos1(pos1),
        .pos2(pos2)
    );

    full_adder fa(
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );

    functional_module func_mod(
        .pos0(pos0),
        .pos1(pos1),
        .pos2(pos2),
        .sum(sum),
        .outv(outv)
    );

    control_logic ctrl(
        .select(select),
        .pos0_en(pos0_en),
        .pos1_en(pos1_en),
        .pos2_en(pos2_en),
        .sum_en(sum_en)
    );


endmodule