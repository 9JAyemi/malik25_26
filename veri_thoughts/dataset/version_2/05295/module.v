module binary_operation_and_counter (
    input clk,
    input reset,
    input up_down,
    input load,
    input [3:0] load_data,
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and_bitwise,
    output out_and_logical,
    output [2:0] out_xor,
    output [5:0] out_not,
    output [3:0] q
);

    // Counter
    reg [3:0] count;
    wire [3:0] count_out;
    
    // Binary Operations
    wire [2:0] a_inv;
    wire [2:0] b_inv;
    wire [2:0] and_bitwise;
    wire and_logical;
    wire [2:0] xor_bitwise;
    
    // MUX
    wire [2:0] mux_out;
    
    // Inverter
    assign out_not = ~{a, b};
    
    // Counter
    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            count <= 0;
        end else if (load == 1) begin
            count <= load_data;
        end else if (up_down == 1) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end
    
    // Binary Operations
    assign a_inv = ~a;
    assign b_inv = ~b;
    assign and_bitwise = a & b;
    assign and_logical = (a != 0) && (b != 0);
    assign xor_bitwise = a ^ b;
    
    // MUX
    assign mux_out = (count_out == 0) ? and_bitwise : count_out;
    
    // Outputs
    assign out_and_bitwise = and_bitwise;
    assign out_and_logical = and_logical;
    assign out_xor = xor_bitwise;
    assign q = count_out;
    
    // Counter Output
    assign count_out = count[3:0];
    
endmodule