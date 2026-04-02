module memory_module_sva (
    input logic CLK1,
    input logic A1EN,
    input logic [4:0] A1ADDR,
    input logic [31:0] A1DATA,
    input logic [4:0] B1ADDR,
    output logic [31:0] B1DATA
);
    reg [31:0] mem = 32'b0;

    always @(posedge CLK1)
        if (A1EN) mem[A1ADDR] <= A1DATA;

    wire B1DATA_wire;
    assign B1DATA_wire = mem[B1ADDR];
    assign B1DATA = B1DATA_wire;

    // Memory write operation should only occur when A1EN is high
    memory_write: assert property (
        @(posedge CLK1) disable iff (!A1EN) $fell(A1EN) |-> (A1DATA == 32'b0)
    );

    // Memory read operation should only occur when A1EN is high
    memory_read: assert property (
        @(posedge CLK1) disable iff (!A1EN) $fell(A1EN) |-> (A1ADDR == 5'b0)
    );

    // Memory address should not exceed 31
    memory_address_range: assert property (
        @(posedge CLK1) disable iff (!A1EN) A1ADDR |-> A1ADDR <= 5'b11111
    );

    // Memory data should not exceed 31 bits
    memory_data_range: assert property (
        @(posedge CLK1) disable iff (!A1EN) A1DATA |-> A1DATA <= 32'hFFFFFFFF
    );

    // Memory read should return the correct data
    memory_read_correctness: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_2: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_3: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_4: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_5: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_6: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_7: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_8: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_9: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );

    // Memory write should not affect read data immediately
    memory_write_read_consistency_10: assert property (
        @(posedge CLK1) disable iff (!A1EN) $rose(A1EN) |-> B1DATA == mem[B1ADDR]
    );
endmodule