module top_module (
    input clk,                 // Clock
    input rst_n,               // Synchronous active-low reset
    input [7:0] data_in,       // 8-bit input data
    output reg [7:0] q         // 8-bit output data
);

    // Internal signals
    wire [23:0] shift_out;
    wire [9:0] accu_out;
    reg [7:0] shift_in;
    reg valid_a;
    wire ready_a;
    reg ready_b;
    
    // Instantiate modules
    shift_register shift_reg (
        .clk(clk),
        .d(shift_in),
        .q(shift_out)
    );
    
    accu accumulator (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(shift_out[7:0]),
        .valid_a(valid_a),
        .ready_b(ready_b),
        .ready_a(ready_a),
        .valid_b(),
        .data_out(accu_out)
    );
    
    // Assign shift_in
    always @ (posedge clk) begin
        if (!rst_n) begin
            shift_in <= 8'b0;
        end else begin
            shift_in <= data_in;
        end
    end
    
    // Assign valid_a and ready_b
    always @ (posedge clk) begin
        if (!rst_n) begin
            valid_a <= 1'b0;
            ready_b <= 1'b0;
        end else begin
            valid_a <= 1'b1;
            ready_b <= ready_a;
        end
    end
    
    // Assign q
    always @ (posedge clk) begin
        if (!rst_n) begin
            q <= 8'b0;
        end else begin
            q <= accu_out[9:2];
        end
    end
    
endmodule

module shift_register (
    input clk,         // Clock
    input [7:0] d,     // 8-bit input data
    output [23:0] q    // 24-bit output data
);
    reg [23:0] shift_reg;
    
    always @ (posedge clk) begin
        shift_reg <= {shift_reg[15:0], d};
    end
    
    assign q = shift_reg;
    
endmodule

module accu(
    input clk,          // Clock
    input rst_n,        // Synchronous active-low reset
    input [7:0] data_in,// 8-bit input data
    input valid_a,      // Valid signal for input data
    input ready_b,      // Ready signal from downstream module
    output ready_a,     // Ready signal for input data
    output reg valid_b, // Valid signal for output data
    output reg [9:0] data_out // 10-bit output data
);
    reg [31:0] accu_reg;
    reg [1:0] count;
    
    always @ (posedge clk) begin
        if (!rst_n) begin
            accu_reg <= 32'b0;
            count <= 2'b0;
            valid_b <= 1'b0;
        end else begin
            if (valid_a && ready_b) begin
                accu_reg <= accu_reg + data_in;
                count <= count + 1;
                if (count == 2) begin
                    valid_b <= 1'b1;
                    data_out <= accu_reg[31:22];
                    accu_reg <= accu_reg[21:0];
                    count <= 2'b0;
                end
            end
        end
    end
    
    assign ready_a = !valid_a || ready_b;
    
endmodule