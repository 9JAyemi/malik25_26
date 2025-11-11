module adder (
    input [3:0] A,
    input [3:0] B,
    input cin,
    output [3:0] sum,
    output cout
);

    assign {cout, sum} = cin + A + B;

endmodule

module ripple_addsub (
    input [3:0] A,
    input [3:0] B,
    input cin,
    input select,
    output [3:0] sum,
    output cout
);

    assign {cout, sum} = select ? (cin + A - B) : (cin + A + B);

endmodule

module top_module (
    input [3:0] A,
    input [3:0] B,
    input cin,
    input select,
    output reg [3:0] sum,
    output reg cout
);

    wire [3:0] adder_out;
    wire adder_cout;
    wire [3:0] ripple_addsub_out;
    wire ripple_addsub_cout;

    adder adder_inst (
        .A(A),
        .B(B),
        .cin(cin),
        .sum(adder_out),
        .cout(adder_cout)
    );

    ripple_addsub ripple_addsub_inst (
        .A(A),
        .B(B),
        .cin(cin),
        .select(select),
        .sum(ripple_addsub_out),
        .cout(ripple_addsub_cout)
    );

    always @(*) begin
        if (select) begin
            if (adder_cout) begin
                sum <= ripple_addsub_out + 4'b0001;
            end else begin
                sum <= ripple_addsub_out;
            end
        end else begin
            sum <= adder_out;
        end
    end

    always @(*) begin
        if (select) begin
            cout <= ripple_addsub_cout;
        end else begin
            cout <= adder_cout;
        end
    end

endmodule