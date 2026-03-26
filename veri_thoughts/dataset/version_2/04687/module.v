
module addsub_16bit (
    input [15:0] in0,
    input [15:0] in1,
    input control,
    output reg [15:0] out
);

    always @ (in0 or in1 or control) begin
        if (control) begin
            out = in0 + in1;
        end else begin
            out = in0 - in1;
        end
    end

endmodule
module comparator_4bit (
    input [3:0] in0,
    input [3:0] in1,
    output reg [3:0] out
);

    always @ (in0 or in1) begin
        if (in0 > in1) begin
            out = 4'b0001;
        end else if (in0 < in1) begin
            out = 4'b0010;
        end else begin
            out = 4'b0111;
        end
    end

endmodule
module top_module (
    input [15:0] in0,
    input [15:0] in1,
    input control,
    output reg [1:0] OUT
);

    wire [15:0] addsub_out;
    wire [3:0] comp_out;

    addsub_16bit addsub_inst (
        .in0(in0),
        .in1(in1),
        .control(control),
        .out(addsub_out)
    );

    comparator_4bit comp_inst (
        .in0(addsub_out[3:0]),
        .in1(in0[3:0]),
        .out(comp_out)
    );

    always @ (addsub_out or comp_out) begin
        if (comp_out == 4'b0001) begin
            OUT <= 2'b01; // in0 > addsub_out
        end else if (comp_out == 4'b0010) begin
            OUT <= 2'b10; // in0 < addsub_out
        end else begin
            OUT <= 2'b11; // in0 == addsub_out
        end
    end

endmodule