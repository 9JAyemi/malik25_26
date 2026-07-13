module memory_module_sva (
    input logic [4:0] A1ADDR,
    input logic A1DATA,
    input logic A1EN,
    input logic CLK1,
    input logic [4:0] B1ADDR,
    input logic B1DATA
);

// B1DATA matches the RTL memory array at B1ADDR on each clock.
    check_b1data_matches_memory: assert property (
        @(posedge CLK1) B1DATA == mem[B1ADDR]
    );

// A1EN high with A1ADDR==0 loads A1DATA into mem[0] on the next clock.
    check_write_addr0: assert property (
        @(posedge CLK1) A1EN && (A1ADDR == 5'd0) |=> (mem[0] == $past(A1DATA))
    );

// A1EN high with A1ADDR==1 loads A1DATA into mem[1] on the next clock.
    check_write_addr1: assert property (
        @(posedge CLK1) A1EN && (A1ADDR == 5'd1) |=> (mem[1] == $past(A1DATA))
    );

// A1EN high with A1ADDR==2 loads A1DATA into mem[2] on the next clock.
    check_write_addr2: assert property (
        @(posedge CLK1) A1EN && (A1ADDR == 5'd2) |=> (mem[2] == $past(A1DATA))
    );

// A1EN high with A1ADDR==3 loads A1DATA into mem[3] on the next clock.
    check_write_addr3: assert property (
        @(posedge CLK1) A1EN && (A1ADDR == 5'd3) |=> (mem[3] == $past(A1DATA))
    );

// A1EN high with A1ADDR==4 loads A1DATA into mem[4] on the next clock.
    check_write_addr4: assert property (
        @(posedge CLK1) A1EN && (A1ADDR == 5'd4) |=> (mem[4] == $past(A1DATA))
    );

// A1EN low leaves mem[0] unchanged on the next clock.
    check_no_write_addr0: assert property (
        @(posedge CLK1) !A1EN && (A1ADDR == 5'd0) |=> (mem[0] == $past(mem[0]))
    );

// A1EN low leaves mem[1] unchanged on the next clock.
    check_no_write_addr1: assert property (
        @(posedge CLK1) !A1EN && (A1ADDR == 5'd1) |=> (mem[1] == $past(mem[1]))
    );

// A1EN low leaves mem[2] unchanged on the next clock.
    check_no_write_addr2: assert property (
        @(posedge CLK1) !A1EN && (A1ADDR == 5'd2) |=> (mem[2] == $past(mem[2]))
    );

// A1EN low leaves mem[3] unchanged on the next clock.
    check_no_write_addr3: assert property (
        @(posedge CLK1) !A1EN && (A1ADDR == 5'd3) |=> (mem[3] == $past(mem[3]))
    );

// A1EN low leaves mem[4] unchanged on the next clock.
    check_no_write_addr4: assert property (
        @(posedge CLK1) !A1EN && (A1ADDR == 5'd4) |=> (mem[4] == $past(mem[4]))
    );

endmodule
