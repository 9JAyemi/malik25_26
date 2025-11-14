module top_module (
    input clk,
    input pause,
    input resume,
    input reset,
    input [7:0] in,
    output [7:0] final_output);

    wire [3:0] counter_output;
    wire [7:0] edge_output;

    decade_counter counter (
        .clk(clk),
        .pause(pause),
        .resume(resume),
        .reset(reset),
        .q(counter_output)
    );

    edge_detection edge_det (
        .clk(clk),
        .in(in),
        .anyedge(edge_output)
    );

    functional_module func_mod (
        .counter_output(counter_output),
        .edge_output(edge_output),
        .final_output(final_output)
    );

endmodule

module decade_counter (
    input clk,
    input pause,
    input resume,
    input reset,
    output [3:0] q
);
    reg [3:0] count;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= 4'b0000;
        end else if (!pause || resume) begin
            count <= (count == 4'b1001) ? 4'b0000 : count + 4'b0001;
        end
    end

    assign q = count;
endmodule

module edge_detection (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);
    reg [7:0] prev_in;
    reg [7:0] edge_count;

    always @(posedge clk) begin
        prev_in <= in;
        edge_count <= edge_count + (in & ~prev_in);
    end

    assign anyedge = edge_count;
endmodule

module functional_module (
    input [3:0] counter_output,
    input [7:0] edge_output,
    output [7:0] final_output
);
    assign final_output = counter_output + edge_output;
endmodule