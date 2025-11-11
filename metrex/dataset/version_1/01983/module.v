
module top_module (
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input select,  // 1 to use adder, 0 to use shifter
    input [31:0] a,  // input for carry select adder
    input [31:0] b,  // input for carry select adder
    input [3:0] data,  // input for barrel shifter
    output reg [31:0] q  // output from selected module
);

    // Define internal signals
    wire [31:0] adder_out;
    wire [3:0] shifter_out;
    reg [3:0] buffer [3:0];
    reg [1:0] buffer_ptr;

    // Define carry select adder
    carry_select_adder adder_inst (
        .a(a),
        .b(b),
        .cin(1'b0),
        .s(adder_out),
        .cout()
    );

    // Define barrel shifter
    always @(posedge clk) begin
        if (areset) begin
            buffer_ptr <= 2'b0;
        end else begin
            if (load) begin
                buffer[buffer_ptr] <= data;
            end else if (ena) begin
                buffer[buffer_ptr] <= {1'b0, buffer[buffer_ptr][3:1]};
            end
            buffer_ptr <= buffer_ptr + 1'b1;
        end
    end
    assign shifter_out = buffer[buffer_ptr];

    // Select output based on select input
    always @(posedge clk) begin
        if (areset) begin
            q <= 32'b0;
        end else begin
            if (select) begin
                q <= adder_out;
            end else begin
                q <= {28'b0, shifter_out};
            end
        end
    end

endmodule
module carry_select_adder (
    input [31:0] a,
    input [31:0] b,
    input cin,
    output reg [31:0] s,
    output reg cout
);
    reg [31:0] p, g;
    reg [4:0] c;

    always @(*) begin
        p = a + b;
        g = a & b;
        c[0] = cin;
        c[1] = g[0] | (p[0] & cin);
        c[2] = g[1] | (p[1] & c[1]);
        c[3] = g[2] | (p[2] & c[2]);
        c[4] = g[3] | (p[3] & c[3]);
        s = p + (c[4] << 4);
        cout = c[4];
    end

endmodule