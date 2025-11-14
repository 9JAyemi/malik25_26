module mux_2to1(OUT,IN0,IN1,S0);
    output OUT;
    input IN0,IN1,S0;
    wire S0_not, IN0_and_not_S0, IN1_and_S0;
    
    not(S0_not,S0);
    and(IN0_and_not_S0, IN0, S0_not);
    and(IN1_and_S0, IN1, S0);
    or(OUT, IN0_and_not_S0, IN1_and_S0);
endmodule