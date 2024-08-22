module tb_arbiter();

    logic clk;
    logic resetn;

    logic [2:0] r;
    logic [2:0] g;

    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk;
    end

    initial begin
        resetn = 1'b0;
        #100
        resetn = 1'b1;
    end

    initial begin
        r = 3'b0;
        #110
        forever begin
            r = 3'b001;
            #25
            r = 3'b010;
            #25
            r = 3'b011;
            #25
            r = 3'b100;
            #25
            r = 3'b101;
            #25
            r = 3'b110;
            #25
            r = 3'b111;
            #25
            $stop();
        end
    end

    arbiter u_arbiter (
        .clk(clk),
        .resetn(resetn),
        .r(r),
        .g(g)
    );


endmodule