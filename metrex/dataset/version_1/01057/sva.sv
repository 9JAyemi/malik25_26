// SVA for signed_multiplier
// Bind this checker to the DUT instance(s).

module signed_multiplier_sva (
    input  logic                  clk,
    input  logic                  rst,
    input  logic                  load_b_i,
    input  logic signed [25:0]    Data_A_i,
    input  logic signed [25:0]    Data_B_i,
    input  logic signed [25:0]    reg_Data_B_i,      // internal
    input  logic signed [51:0]    reg_sgf_result_o,  // internal
    input  logic signed [51:0]    sgf_result_o
);
    default clocking cb @(posedge clk); endclocking

    // Constants
    localparam signed [25:0] S26_MIN = -26'sd33554432;
    localparam signed [25:0] S26_MAX =  26'sd33554431;

    // Reset behavior
    assert property (@cb rst |=> (reg_Data_B_i==0 && reg_sgf_result_o==0 && sgf_result_o==0));
    assert property (@cb (!rst && $past(rst)) |-> (sgf_result_o==0)); // first active cycle result is 0

    // Output mirrors registered result
    assert property (@cb sgf_result_o == reg_sgf_result_o);

    // reg_Data_B_i update/hold
    assert property (disable iff (rst) (load_b_i |=> reg_Data_B_i == $past(Data_B_i)));
    assert property (disable iff (rst) (!load_b_i |=> reg_Data_B_i == $past(reg_Data_B_i)));

    // Core functional correctness (1-cycle latency, uses prior reg_Data_B_i)
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) |-> 
        (sgf_result_o == $signed($past(Data_A_i)) * $signed($past(reg_Data_B_i)))
    );

    // No X on state/output after reset
    assert property (disable iff (rst) !$isunknown({reg_Data_B_i, reg_sgf_result_o, sgf_result_o}));

    // Algebraic identities (signed)
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(Data_A_i)==0 || $past(reg_Data_B_i)==0) |-> (sgf_result_o==0)
    );
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(Data_A_i)==26'sd1) |-> (sgf_result_o == $past(reg_Data_B_i))
    );
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(Data_A_i)==-26'sd1) |-> (sgf_result_o == -$past(reg_Data_B_i))
    );
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(reg_Data_B_i)==26'sd1) |-> (sgf_result_o == $past(Data_A_i))
    );
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(reg_Data_B_i)==-26'sd1) |-> (sgf_result_o == -$past(Data_A_i))
    );

    // Sign correctness when neither operand is zero
    assert property (disable iff (rst)
        (!$isunknown($past({Data_A_i, reg_Data_B_i}))) &&
        ($past(Data_A_i)!=0) && ($past(reg_Data_B_i)!=0) |-> 
        (sgf_result_o[51] == ($past(Data_A_i[25]) ^ $past(reg_Data_B_i[25])))
    );

    // Coverage: load/pipeline usage
    cover property (@cb !rst && load_b_i);                                    // observe loads
    cover property (disable iff (rst) load_b_i && (Data_B_i != reg_Data_B_i)) // load when new B != held B
    ;

    // Coverage: operand patterns observed at multiplier input stage (1-cycle prior)
    cover property (disable iff (rst) $past(Data_A_i)==0);
    cover property (disable iff (rst) $past(reg_Data_B_i)==0);
    cover property (disable iff (rst) $past(Data_A_i)==26'sd1);
    cover property (disable iff (rst) $past(Data_A_i)==-26'sd1);
    cover property (disable iff (rst) $past(reg_Data_B_i)==26'sd1);
    cover property (disable iff (rst) $past(reg_Data_B_i)==-26'sd1);
    cover property (disable iff (rst) $past(Data_A_i)==S26_MAX);
    cover property (disable iff (rst) $past(Data_A_i)==S26_MIN);
    cover property (disable iff (rst) $past(reg_Data_B_i)==S26_MAX);
    cover property (disable iff (rst) $past(reg_Data_B_i)==S26_MIN);
    // Coverage: sign combinations
    cover property (disable iff (rst) ($past(Data_A_i[25])==0 && $past(reg_Data_B_i[25])==0));
    cover property (disable iff (rst) ($past(Data_A_i[25])==1 && $past(reg_Data_B_i[25])==0));
    cover property (disable iff (rst) ($past(Data_A_i[25])==0 && $past(reg_Data_B_i[25])==1));
    cover property (disable iff (rst) ($past(Data_A_i[25])==1 && $past(reg_Data_B_i[25])==1));
endmodule

// Bind into the DUT (place after DUT definition)
bind signed_multiplier signed_multiplier_sva
u_signed_multiplier_sva (
    .clk              (clk),
    .rst              (rst),
    .load_b_i         (load_b_i),
    .Data_A_i         (Data_A_i),
    .Data_B_i         (Data_B_i),
    .reg_Data_B_i     (reg_Data_B_i),
    .reg_sgf_result_o (reg_sgf_result_o),
    .sgf_result_o     (sgf_result_o)
);