module nor_gate(
    input a,
    input b,
    output out
    );
    
    assign out = ~(a | b);
    
endmodule

module mux_with_nor_gate(
    input a,
    input b,
    input c,
    input control,
    output w,
    output x,
    output y,
    output z
    );
    
    wire nor_out;
    nor_gate nor_inst(a, b, nor_out);
    
    assign w = (control == 1'b0) ? a : ((control == 1'b1) ? b : c);
    assign x = w;
    assign y = w;
    assign z = w;
    
endmodule