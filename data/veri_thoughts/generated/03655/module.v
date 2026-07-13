module not_gate( input in, output out );
    assign out = ~(in & in);
endmodule