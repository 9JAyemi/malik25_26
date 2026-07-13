module register_4bit (
    input CLK,
    input [3:0] D,
    input LD,
    input RST,
    output reg [3:0] Q
);

    // Local signals
    reg [3:0] reg_Q;
    reg [3:0] reg_Q_N;
    reg [3:0] mux_out;
    reg [3:0] rst_d;

    // Instantiate the flip-flop modules
    always @(posedge CLK or posedge RST) begin
        if (RST) begin
            reg_Q <= 4'b0;
        end else begin
            reg_Q <= mux_out;
        end
    end

    // 4-to-1 multiplexer to select between D input and buffered output
    always @* begin
        mux_out[0] = (LD) ? D[0] : reg_Q[0];
        mux_out[1] = (LD) ? D[1] : reg_Q[1];
        mux_out[2] = (LD) ? D[2] : reg_Q[2];
        mux_out[3] = (LD) ? D[3] : reg_Q[3];
    end

    // Asynchronous reset
    always @* begin
        rst_d = (RST) ? 4'b0 : 4'b1;
    end

    // Output
    always @* begin
        Q = reg_Q;
    end

endmodule