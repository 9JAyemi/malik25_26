
module grey_counter(
    input clk,
    output [3:0] q
);

    reg [3:0] q_reg;

    always @(posedge clk) begin
        q_reg <= q_reg + 1;
        if (q_reg == 4'b1111) begin
            q_reg <= 4'b0000;
        end
    end

    assign q = q_reg;

endmodule
module slow_oscillator(
    input rstn,
    input osc_clk,
    output [3:0] led,
    output clk
);

    reg [22:0] c_delay;
    
    // Gray counter
    grey_counter_4bit gc1(.clk(osc_clk), .q(led));
    
    // Counter to slow down the internal oscillator output
    always @(posedge osc_clk or negedge rstn) begin
        if (~rstn) begin
            c_delay <= 23'h000000;
        end else begin
            c_delay <= c_delay + 1;
        end
    end
    
    // Output clock signal
    assign clk = c_delay[22];
    
endmodule
module grey_counter_4bit(
    input clk,
    output [3:0] q
);

    reg [3:0] q_reg;

    always @(posedge clk) begin
        q_reg <= q_reg + 1;
        if (q_reg == 4'b1111) begin
            q_reg <= 4'b0000;
        end
    end

    assign q = q_reg;

endmodule