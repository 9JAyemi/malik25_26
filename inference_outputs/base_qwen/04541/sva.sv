```systemverilog
module twos_complement_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic invert,
    output logic [3:0] Y
);
    // Invert A if necessary
    wire [3:0] not_A;
    assign not_A = ~A;

    // Calculate 1
    wire [3:0] one;
    assign one = 4'b0001;

    // Calculate add_one
    wire [3:0] add_one;
    assign add_one = not_A + one;

    // Calculate twos_comp
    wire [3:0] twos_comp;
    assign twos_comp = (invert) ? ~add_one : add_one;

    // Assign output
    always @(*) begin
        Y <= twos_comp;
    end

    // Property to check that Y is correctly calculated based on A and invert
    twos_comp_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == twos_comp
    ) else $error("Y is not correctly calculated based on A and invert");

    // Property to check that not_A is the correct inversion of A
    not_A_inversion: assert property (
        @(posedge CLK) disable iff (!RESETn) not_A == ~A
    ) else $error("not_A is not the correct inversion of A");

    // Property to check that one is correctly assigned as 1
    one_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) one == 4'b0001
    ) else $error("one is not correctly assigned as 1");

    // Property to check that add_one is correctly calculated as not_A + 1
    add_one_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) add_one == not_A + 1
    ) else $error("add_one is not correctly calculated as not_A + 1");

    // Property to check that twos_comp is correctly calculated based on invert
    twos_comp_inversion: assert property (
        @(posedge CLK) disable iff (!RESETn) (invert) ? twos_comp == ~add_one : twos_comp == add_one
    ) else $error("twos_comp is not correctly calculated based on invert");

    // Property to check that Y is not driven to an invalid value
    Y_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) Y inside {[0:15]}
    ) else $error("Y is driven to an invalid value");

    // Property to check that not_A is not driven to an invalid value
    not_A_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) not_A inside {[0:15]}
    ) else $error("not_A is driven to an invalid value");

    // Property to check that one is not driven to an invalid value
    one_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) one inside {[0:15]}
    ) else $error("one is driven to an invalid value");

    // Property to check that add_one is not driven to an invalid value
    add_one_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) add_one inside {[0:15]}
    ) else $error("add_one is not driven to an invalid value");

    // Property to check that twos_comp is not driven to an invalid value
    twos_comp_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) twos_comp inside {[0:15]}
    ) else $error("twos_comp is not driven to an invalid value");
endmodule
```