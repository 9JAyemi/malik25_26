module ThermoGauge(
    gauge,
    value,
    enable,
    enforce
);

    parameter LOGWORD = 0;
    localparam WORD = (1<<LOGWORD);

    output wire [WORD-1:0] gauge;
    input [LOGWORD-1:0] value;
    input enable;
    input enforce;

    wire [WORD-1:0] shifted_value;
    wire [WORD-1:0] shifted_value_plus_one;

    assign shifted_value = {1'b0, value};
    assign shifted_value_plus_one = shifted_value + 1'b1;

    assign gauge = (enable && !enforce) ? shifted_value_plus_one : shifted_value;

endmodule