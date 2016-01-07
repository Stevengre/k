// Copyright (c) 2014-2016 K Team. All Rights Reserved.

package org.kframework.kore.compile;

import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.kore.convertors.TstTinyOnKORE_IT;
import org.kframework.parser.ProductionReference;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.unparser.AddBrackets;
import org.kframework.unparser.KOREToTreeNodes;
import org.kframework.utils.KoreUtils;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.*;

public class StrategiesTest {

    @org.junit.Rule
    public TestName name = new TestName();

    protected File testResource(String baseName) throws URISyntaxException {
        return new File(TstTinyOnKORE_IT.class.getResource(baseName).toURI());
    }

    @Test
    public void simple() throws IOException, URISyntaxException {
        String filename = "/compiler-tests/strategies.k";
        String mainModule = "A";
        String syntaxModule = "A";

        String pgm = "x";
        String expected = "<t> <k> zz ~> . </k> <s> false ~> . </s> </t>";

        assertSearch(filename, mainModule, syntaxModule, pgm, expected, "if ^xy ; ^xy then ^xy else ^xz ; ^zzz ; ^zzz");
    }

    @Test
    public void imp() throws IOException, URISyntaxException {
        String filename = "/compiler-tests/strategies_imp.k";
        String mainModule = "IMP";
        String syntaxModule = "IMP-SYNTAX";

        String pgm = "int s, n; n = 10; while(0<=n) { s = s + n; n = n + -1; }";
        String expected = "<generatedTop> <k> . </k> <state> s |-> 55 n |-> -1 </state> <s> true ~> . </s> </generatedTop>";

        assertSearch(filename, mainModule, syntaxModule, pgm, expected, "(^heat* ; ^regular ; (^cool || true))*"); //
    }

    private void assertSearch(String filename, String mainModule, String syntaxModule, String pgm, String expected, String strategies) throws URISyntaxException, IOException {
        KoreUtils utils = new KoreUtils(filename, mainModule, syntaxModule, true, KORE.Sort("Exp") ,true, true);
        K kPgm = utils.getParsed(pgm, Source.apply("generated by " + getClass().getSimpleName()), strategies);

        Rewriter rewriter = utils.getRewriter();

        List<? extends Map<? extends KVariable, ? extends K>> searchResults = rewriter.search(kPgm, Optional.empty(), Optional.empty(),
                new Rule(KORE.KVariable("X"), BooleanUtils.TRUE, BooleanUtils.TRUE, KORE.Att()),
                SearchType.FINAL);

        List<K> res = searchResults.stream().flatMap(m -> m.values().stream()).collect(Collectors.toList());
        Module unparsingModule = utils.getUnparsingModule();

        Stream<String> sRes = res.stream().map(k -> KOREToTreeNodes.toString(new AddBrackets(unparsingModule).addBrackets((ProductionReference) KOREToTreeNodes.apply(KOREToTreeNodes.up(unparsingModule, k), unparsingModule))));
        String actual = sRes.reduce("", (a, b) -> a + "\n" + b).trim();

        assertEquals("Execution failed", expected, actual);
    }

}
