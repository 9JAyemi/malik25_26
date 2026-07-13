
module sky130_fd_sc_hd__mux2_1 (
    input  A,
    input  B,
    input  S,
    output Z
);

    assign Z = S ? B : A;

endmodule
module binary_counter(
    input clk,
    input rst,
    output reg [3:0] count
);

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    
    always @(posedge clk, posedge rst) begin
        if (rst) begin
            count <= 4'b0;
        end else begin
            count <= count + 4'b1;
            if (count == 4'b1111) begin
                count <= 4'b0;
            end
        end
    end
    
    // Instantiate sky130_fd_sc_hd__mux2_1 module
    wire mux_out;
    sky130_fd_sc_hd__mux2_1 mux_inst (.Z(mux_out), .A(4'b0), .B(count[0]), .S(count[0]));
    
endmodule